import LonelyRunner.LRC.Spec.OrderSevenP2BitsN
import LonelyRunner.LRC.Spec.OrderSevenP2C0N
import LonelyRunner.LRC.Spec.OrderSevenP2C1N
import LonelyRunner.LRC.Spec.OrderSevenP2C2N
import LonelyRunner.LRC.Spec.OrderSevenP2C3N
import LonelyRunner.LRC.Spec.OrderSevenP2C4N
import LonelyRunner.LRC.Spec.OrderSevenP2C5N
import LonelyRunner.LRC.Spec.OrderSevenP2C6N
import LonelyRunner.LRC.Spec.OrderSevenP2C7N
import LonelyRunner.LRC.Spec.OrderSevenP2C8N
import LonelyRunner.LRC.Spec.OrderSevenP2C9N

set_option maxRecDepth 100000

namespace LRC.O7P2

theorem qroot_0 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 0) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_0_0, decode 300 e_0_1, decode 300 e_0_2, decode 300 e_0_3, decode 300 e_0_4, decode 300 e_0_5, decode 171 e_0_6] (fun x hx => ab_bits hx) qcov_0 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_0_0, qch_0_1, qch_0_2, qch_0_3, qch_0_4, qch_0_5, qch_0_6])

theorem qroot_1 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 1) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_1_0, decode 300 e_1_1, decode 300 e_1_2, decode 300 e_1_3, decode 300 e_1_4, decode 300 e_1_5, decode 171 e_1_6] (fun x hx => ab_bits hx) qcov_1 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_1_0, qch_1_1, qch_1_2, qch_1_3, qch_1_4, qch_1_5, qch_1_6])

theorem qroot_2 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 2) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_2_0, decode 300 e_2_1, decode 300 e_2_2, decode 300 e_2_3, decode 300 e_2_4, decode 300 e_2_5, decode 171 e_2_6] (fun x hx => ab_bits hx) qcov_2 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_2_0, qch_2_1, qch_2_2, qch_2_3, qch_2_4, qch_2_5, qch_2_6])

theorem qroot_3 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 3) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_3_0, decode 300 e_3_1, decode 300 e_3_2, decode 300 e_3_3, decode 300 e_3_4, decode 300 e_3_5, decode 171 e_3_6] (fun x hx => ab_bits hx) qcov_3 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_3_0, qch_3_1, qch_3_2, qch_3_3, qch_3_4, qch_3_5, qch_3_6])

theorem qroot_4 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 4) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_4_0, decode 300 e_4_1, decode 300 e_4_2, decode 300 e_4_3, decode 300 e_4_4, decode 300 e_4_5, decode 171 e_4_6] (fun x hx => ab_bits hx) qcov_4 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_4_0, qch_4_1, qch_4_2, qch_4_3, qch_4_4, qch_4_5, qch_4_6])

theorem qroot_5 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 5) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_5_0, decode 300 e_5_1, decode 300 e_5_2, decode 300 e_5_3, decode 300 e_5_4, decode 300 e_5_5, decode 171 e_5_6] (fun x hx => ab_bits hx) qcov_5 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_5_0, qch_5_1, qch_5_2, qch_5_3, qch_5_4, qch_5_5, qch_5_6])

theorem qroot_6 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 6) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_6_0, decode 300 e_6_1, decode 300 e_6_2, decode 300 e_6_3, decode 300 e_6_4, decode 300 e_6_5, decode 171 e_6_6] (fun x hx => ab_bits hx) qcov_6 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_6_0, qch_6_1, qch_6_2, qch_6_3, qch_6_4, qch_6_5, qch_6_6])

theorem qroot_7 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 7) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_7_0, decode 300 e_7_1, decode 300 e_7_2, decode 300 e_7_3, decode 300 e_7_4, decode 300 e_7_5, decode 171 e_7_6] (fun x hx => ab_bits hx) qcov_7 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_7_0, qch_7_1, qch_7_2, qch_7_3, qch_7_4, qch_7_5, qch_7_6])

theorem qroot_8 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 8) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_8_0, decode 300 e_8_1, decode 300 e_8_2, decode 300 e_8_3, decode 300 e_8_4, decode 300 e_8_5, decode 171 e_8_6] (fun x hx => ab_bits hx) qcov_8 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_8_0, qch_8_1, qch_8_2, qch_8_3, qch_8_4, qch_8_5, qch_8_6])

theorem qroot_9 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 9) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_9_0, decode 300 e_9_1, decode 300 e_9_2, decode 300 e_9_3, decode 300 e_9_4, decode 300 e_9_5, decode 171 e_9_6] (fun x hx => ab_bits hx) qcov_9 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_9_0, qch_9_1, qch_9_2, qch_9_3, qch_9_4, qch_9_5, qch_9_6])

theorem qroot_10 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 10) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_10_0, decode 300 e_10_1, decode 300 e_10_2, decode 300 e_10_3, decode 300 e_10_4, decode 300 e_10_5, decode 171 e_10_6] (fun x hx => ab_bits hx) qcov_10 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_10_0, qch_10_1, qch_10_2, qch_10_3, qch_10_4, qch_10_5, qch_10_6])

theorem qroot_11 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 11) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_11_0, decode 300 e_11_1, decode 300 e_11_2, decode 300 e_11_3, decode 300 e_11_4, decode 300 e_11_5, decode 171 e_11_6] (fun x hx => ab_bits hx) qcov_11 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_11_0, qch_11_1, qch_11_2, qch_11_3, qch_11_4, qch_11_5, qch_11_6])

theorem qroot_12 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 12) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_12_0, decode 300 e_12_1, decode 300 e_12_2, decode 300 e_12_3, decode 300 e_12_4, decode 300 e_12_5, decode 171 e_12_6] (fun x hx => ab_bits hx) qcov_12 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_12_0, qch_12_1, qch_12_2, qch_12_3, qch_12_4, qch_12_5, qch_12_6])

theorem qroot_13 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 13) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_13_0, decode 300 e_13_1, decode 300 e_13_2, decode 300 e_13_3, decode 300 e_13_4, decode 300 e_13_5, decode 171 e_13_6] (fun x hx => ab_bits hx) qcov_13 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_13_0, qch_13_1, qch_13_2, qch_13_3, qch_13_4, qch_13_5, qch_13_6])

theorem qroot_14 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 14) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_14_0, decode 300 e_14_1, decode 300 e_14_2, decode 300 e_14_3, decode 300 e_14_4, decode 300 e_14_5, decode 171 e_14_6] (fun x hx => ab_bits hx) qcov_14 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_14_0, qch_14_1, qch_14_2, qch_14_3, qch_14_4, qch_14_5, qch_14_6])

theorem qroot_15 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 15) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_15_0, decode 300 e_15_1, decode 300 e_15_2, decode 300 e_15_3, decode 300 e_15_4, decode 300 e_15_5, decode 171 e_15_6] (fun x hx => ab_bits hx) qcov_15 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_15_0, qch_15_1, qch_15_2, qch_15_3, qch_15_4, qch_15_5, qch_15_6])

theorem qroot_16 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 16) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_16_0, decode 300 e_16_1, decode 300 e_16_2, decode 300 e_16_3, decode 300 e_16_4, decode 300 e_16_5, decode 171 e_16_6] (fun x hx => ab_bits hx) qcov_16 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_16_0, qch_16_1, qch_16_2, qch_16_3, qch_16_4, qch_16_5, qch_16_6])

theorem qroot_17 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 17) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_17_0, decode 300 e_17_1, decode 300 e_17_2, decode 300 e_17_3, decode 300 e_17_4, decode 300 e_17_5, decode 171 e_17_6] (fun x hx => ab_bits hx) qcov_17 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_17_0, qch_17_1, qch_17_2, qch_17_3, qch_17_4, qch_17_5, qch_17_6])

theorem qroot_18 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 18) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_18_0, decode 300 e_18_1, decode 300 e_18_2, decode 300 e_18_3, decode 300 e_18_4, decode 300 e_18_5, decode 171 e_18_6] (fun x hx => ab_bits hx) qcov_18 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_18_0, qch_18_1, qch_18_2, qch_18_3, qch_18_4, qch_18_5, qch_18_6])

theorem qroot_19 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 19) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_19_0, decode 300 e_19_1, decode 300 e_19_2, decode 300 e_19_3, decode 300 e_19_4, decode 300 e_19_5, decode 171 e_19_6] (fun x hx => ab_bits hx) qcov_19 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_19_0, qch_19_1, qch_19_2, qch_19_3, qch_19_4, qch_19_5, qch_19_6])

theorem qroot_20 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 20) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_20_0, decode 300 e_20_1, decode 300 e_20_2, decode 300 e_20_3, decode 300 e_20_4, decode 300 e_20_5, decode 171 e_20_6] (fun x hx => ab_bits hx) qcov_20 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_20_0, qch_20_1, qch_20_2, qch_20_3, qch_20_4, qch_20_5, qch_20_6])

theorem qroot_21 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 21) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_21_0, decode 300 e_21_1, decode 300 e_21_2, decode 300 e_21_3, decode 300 e_21_4, decode 300 e_21_5, decode 171 e_21_6] (fun x hx => ab_bits hx) qcov_21 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_21_0, qch_21_1, qch_21_2, qch_21_3, qch_21_4, qch_21_5, qch_21_6])

theorem qroot_22 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 22) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_22_0, decode 300 e_22_1, decode 300 e_22_2, decode 300 e_22_3, decode 300 e_22_4, decode 300 e_22_5, decode 171 e_22_6] (fun x hx => ab_bits hx) qcov_22 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_22_0, qch_22_1, qch_22_2, qch_22_3, qch_22_4, qch_22_5, qch_22_6])

theorem qroot_23 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 23) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_23_0, decode 300 e_23_1, decode 300 e_23_2, decode 300 e_23_3, decode 300 e_23_4, decode 300 e_23_5, decode 171 e_23_6] (fun x hx => ab_bits hx) qcov_23 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_23_0, qch_23_1, qch_23_2, qch_23_3, qch_23_4, qch_23_5, qch_23_6])

theorem qroot_24 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 24) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_24_0, decode 300 e_24_1, decode 300 e_24_2, decode 300 e_24_3, decode 300 e_24_4, decode 300 e_24_5, decode 171 e_24_6] (fun x hx => ab_bits hx) qcov_24 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_24_0, qch_24_1, qch_24_2, qch_24_3, qch_24_4, qch_24_5, qch_24_6])

theorem qroot_25 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 25) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_25_0, decode 300 e_25_1, decode 300 e_25_2, decode 300 e_25_3, decode 300 e_25_4, decode 300 e_25_5, decode 171 e_25_6] (fun x hx => ab_bits hx) qcov_25 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_25_0, qch_25_1, qch_25_2, qch_25_3, qch_25_4, qch_25_5, qch_25_6])

theorem qroot_26 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 26) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_26_0, decode 300 e_26_1, decode 300 e_26_2, decode 300 e_26_3, decode 300 e_26_4, decode 300 e_26_5, decode 171 e_26_6] (fun x hx => ab_bits hx) qcov_26 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_26_0, qch_26_1, qch_26_2, qch_26_3, qch_26_4, qch_26_5, qch_26_6])

theorem qroot_27 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 27) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_27_0, decode 300 e_27_1, decode 300 e_27_2, decode 300 e_27_3, decode 300 e_27_4, decode 300 e_27_5, decode 171 e_27_6] (fun x hx => ab_bits hx) qcov_27 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_27_0, qch_27_1, qch_27_2, qch_27_3, qch_27_4, qch_27_5, qch_27_6])

theorem qroot_28 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 28) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_28_0, decode 300 e_28_1, decode 300 e_28_2, decode 300 e_28_3, decode 300 e_28_4, decode 300 e_28_5, decode 171 e_28_6] (fun x hx => ab_bits hx) qcov_28 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_28_0, qch_28_1, qch_28_2, qch_28_3, qch_28_4, qch_28_5, qch_28_6])

theorem qroot_29 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 29) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_29_0, decode 300 e_29_1, decode 300 e_29_2, decode 300 e_29_3, decode 300 e_29_4, decode 300 e_29_5, decode 171 e_29_6] (fun x hx => ab_bits hx) qcov_29 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_29_0, qch_29_1, qch_29_2, qch_29_3, qch_29_4, qch_29_5, qch_29_6])

theorem qroot_30 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 30) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_30_0, decode 300 e_30_1, decode 300 e_30_2, decode 300 e_30_3, decode 300 e_30_4, decode 300 e_30_5, decode 171 e_30_6] (fun x hx => ab_bits hx) qcov_30 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_30_0, qch_30_1, qch_30_2, qch_30_3, qch_30_4, qch_30_5, qch_30_6])

theorem qroot_31 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 31) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_31_0, decode 300 e_31_1, decode 300 e_31_2, decode 300 e_31_3, decode 300 e_31_4, decode 300 e_31_5, decode 171 e_31_6] (fun x hx => ab_bits hx) qcov_31 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_31_0, qch_31_1, qch_31_2, qch_31_3, qch_31_4, qch_31_5, qch_31_6])

theorem qroot_32 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 32) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_32_0, decode 300 e_32_1, decode 300 e_32_2, decode 300 e_32_3, decode 300 e_32_4, decode 300 e_32_5, decode 171 e_32_6] (fun x hx => ab_bits hx) qcov_32 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_32_0, qch_32_1, qch_32_2, qch_32_3, qch_32_4, qch_32_5, qch_32_6])

theorem qroot_33 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 33) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_33_0, decode 300 e_33_1, decode 300 e_33_2, decode 300 e_33_3, decode 300 e_33_4, decode 300 e_33_5, decode 171 e_33_6] (fun x hx => ab_bits hx) qcov_33 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_33_0, qch_33_1, qch_33_2, qch_33_3, qch_33_4, qch_33_5, qch_33_6])

theorem qroot_34 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 34) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_34_0, decode 300 e_34_1, decode 300 e_34_2, decode 300 e_34_3, decode 300 e_34_4, decode 300 e_34_5, decode 171 e_34_6] (fun x hx => ab_bits hx) qcov_34 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_34_0, qch_34_1, qch_34_2, qch_34_3, qch_34_4, qch_34_5, qch_34_6])

theorem qroot_35 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 35) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_35_0, decode 300 e_35_1, decode 300 e_35_2, decode 300 e_35_3, decode 300 e_35_4, decode 300 e_35_5, decode 171 e_35_6] (fun x hx => ab_bits hx) qcov_35 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_35_0, qch_35_1, qch_35_2, qch_35_3, qch_35_4, qch_35_5, qch_35_6])

theorem qroot_36 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 36) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_36_0, decode 300 e_36_1, decode 300 e_36_2, decode 300 e_36_3, decode 300 e_36_4, decode 300 e_36_5, decode 171 e_36_6] (fun x hx => ab_bits hx) qcov_36 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_36_0, qch_36_1, qch_36_2, qch_36_3, qch_36_4, qch_36_5, qch_36_6])

theorem qroot_37 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 37) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_37_0, decode 300 e_37_1, decode 300 e_37_2, decode 300 e_37_3, decode 300 e_37_4, decode 300 e_37_5, decode 171 e_37_6] (fun x hx => ab_bits hx) qcov_37 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_37_0, qch_37_1, qch_37_2, qch_37_3, qch_37_4, qch_37_5, qch_37_6])

theorem qroot_38 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 38) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_38_0, decode 300 e_38_1, decode 300 e_38_2, decode 300 e_38_3, decode 300 e_38_4, decode 300 e_38_5, decode 171 e_38_6] (fun x hx => ab_bits hx) qcov_38 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_38_0, qch_38_1, qch_38_2, qch_38_3, qch_38_4, qch_38_5, qch_38_6])

theorem qroot_39 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 39) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_39_0, decode 300 e_39_1, decode 300 e_39_2, decode 300 e_39_3, decode 300 e_39_4, decode 300 e_39_5, decode 171 e_39_6] (fun x hx => ab_bits hx) qcov_39 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_39_0, qch_39_1, qch_39_2, qch_39_3, qch_39_4, qch_39_5, qch_39_6])

theorem qroot_40 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 40) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_40_0, decode 300 e_40_1, decode 300 e_40_2, decode 300 e_40_3, decode 300 e_40_4, decode 300 e_40_5, decode 171 e_40_6] (fun x hx => ab_bits hx) qcov_40 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_40_0, qch_40_1, qch_40_2, qch_40_3, qch_40_4, qch_40_5, qch_40_6])

theorem qroot_41 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 41) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_41_0, decode 300 e_41_1, decode 300 e_41_2, decode 300 e_41_3, decode 300 e_41_4, decode 300 e_41_5, decode 171 e_41_6] (fun x hx => ab_bits hx) qcov_41 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_41_0, qch_41_1, qch_41_2, qch_41_3, qch_41_4, qch_41_5, qch_41_6])

theorem qroot_42 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 42) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_42_0, decode 300 e_42_1, decode 300 e_42_2, decode 300 e_42_3, decode 300 e_42_4, decode 300 e_42_5, decode 174 e_42_6] (fun x hx => ab_bits hx) qcov_42 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_42_0, qch_42_1, qch_42_2, qch_42_3, qch_42_4, qch_42_5, qch_42_6])

theorem qroot_43 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 43) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_43_0, decode 300 e_43_1, decode 300 e_43_2, decode 300 e_43_3, decode 300 e_43_4, decode 300 e_43_5, decode 174 e_43_6] (fun x hx => ab_bits hx) qcov_43 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_43_0, qch_43_1, qch_43_2, qch_43_3, qch_43_4, qch_43_5, qch_43_6])

theorem qroot_44 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 44) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_44_0, decode 300 e_44_1, decode 300 e_44_2, decode 300 e_44_3, decode 300 e_44_4, decode 300 e_44_5, decode 174 e_44_6] (fun x hx => ab_bits hx) qcov_44 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_44_0, qch_44_1, qch_44_2, qch_44_3, qch_44_4, qch_44_5, qch_44_6])

theorem qroot_45 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 45) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_45_0, decode 300 e_45_1, decode 300 e_45_2, decode 300 e_45_3, decode 300 e_45_4, decode 300 e_45_5, decode 174 e_45_6] (fun x hx => ab_bits hx) qcov_45 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_45_0, qch_45_1, qch_45_2, qch_45_3, qch_45_4, qch_45_5, qch_45_6])

theorem qroot_46 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 46) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_46_0, decode 300 e_46_1, decode 300 e_46_2, decode 300 e_46_3, decode 300 e_46_4, decode 300 e_46_5, decode 174 e_46_6] (fun x hx => ab_bits hx) qcov_46 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_46_0, qch_46_1, qch_46_2, qch_46_3, qch_46_4, qch_46_5, qch_46_6])

theorem qroot_47 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 47) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_47_0, decode 300 e_47_1, decode 300 e_47_2, decode 300 e_47_3, decode 300 e_47_4, decode 300 e_47_5, decode 174 e_47_6] (fun x hx => ab_bits hx) qcov_47 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_47_0, qch_47_1, qch_47_2, qch_47_3, qch_47_4, qch_47_5, qch_47_6])

theorem qroot_48 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 48) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_48_0, decode 300 e_48_1, decode 300 e_48_2, decode 300 e_48_3, decode 300 e_48_4, decode 300 e_48_5, decode 174 e_48_6] (fun x hx => ab_bits hx) qcov_48 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_48_0, qch_48_1, qch_48_2, qch_48_3, qch_48_4, qch_48_5, qch_48_6])

theorem qroot_49 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 49) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_49_0, decode 300 e_49_1, decode 300 e_49_2, decode 300 e_49_3, decode 300 e_49_4, decode 300 e_49_5, decode 174 e_49_6] (fun x hx => ab_bits hx) qcov_49 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_49_0, qch_49_1, qch_49_2, qch_49_3, qch_49_4, qch_49_5, qch_49_6])

theorem qroot_50 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 50) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_50_0, decode 300 e_50_1, decode 300 e_50_2, decode 300 e_50_3, decode 300 e_50_4, decode 300 e_50_5, decode 174 e_50_6] (fun x hx => ab_bits hx) qcov_50 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_50_0, qch_50_1, qch_50_2, qch_50_3, qch_50_4, qch_50_5, qch_50_6])

theorem qroot_51 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 51) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_51_0, decode 300 e_51_1, decode 300 e_51_2, decode 300 e_51_3, decode 300 e_51_4, decode 300 e_51_5, decode 174 e_51_6] (fun x hx => ab_bits hx) qcov_51 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_51_0, qch_51_1, qch_51_2, qch_51_3, qch_51_4, qch_51_5, qch_51_6])

theorem qroot_52 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 52) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_52_0, decode 300 e_52_1, decode 300 e_52_2, decode 300 e_52_3, decode 300 e_52_4, decode 300 e_52_5, decode 174 e_52_6] (fun x hx => ab_bits hx) qcov_52 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_52_0, qch_52_1, qch_52_2, qch_52_3, qch_52_4, qch_52_5, qch_52_6])

theorem qroot_53 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 53) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_53_0, decode 300 e_53_1, decode 300 e_53_2, decode 300 e_53_3, decode 300 e_53_4, decode 300 e_53_5, decode 174 e_53_6] (fun x hx => ab_bits hx) qcov_53 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_53_0, qch_53_1, qch_53_2, qch_53_3, qch_53_4, qch_53_5, qch_53_6])

theorem qroot_54 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 54) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_54_0, decode 300 e_54_1, decode 300 e_54_2, decode 300 e_54_3, decode 300 e_54_4, decode 300 e_54_5, decode 174 e_54_6] (fun x hx => ab_bits hx) qcov_54 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_54_0, qch_54_1, qch_54_2, qch_54_3, qch_54_4, qch_54_5, qch_54_6])

theorem qroot_55 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 55) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_55_0, decode 300 e_55_1, decode 300 e_55_2, decode 300 e_55_3, decode 300 e_55_4, decode 300 e_55_5, decode 174 e_55_6] (fun x hx => ab_bits hx) qcov_55 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_55_0, qch_55_1, qch_55_2, qch_55_3, qch_55_4, qch_55_5, qch_55_6])

theorem qroot_56 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 56) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_56_0, decode 300 e_56_1, decode 300 e_56_2, decode 300 e_56_3, decode 300 e_56_4, decode 300 e_56_5, decode 174 e_56_6] (fun x hx => ab_bits hx) qcov_56 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_56_0, qch_56_1, qch_56_2, qch_56_3, qch_56_4, qch_56_5, qch_56_6])

theorem qroot_57 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 57) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_57_0, decode 300 e_57_1, decode 300 e_57_2, decode 300 e_57_3, decode 300 e_57_4, decode 300 e_57_5, decode 174 e_57_6] (fun x hx => ab_bits hx) qcov_57 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_57_0, qch_57_1, qch_57_2, qch_57_3, qch_57_4, qch_57_5, qch_57_6])

theorem qroot_58 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 58) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_58_0, decode 300 e_58_1, decode 300 e_58_2, decode 300 e_58_3, decode 300 e_58_4, decode 300 e_58_5, decode 174 e_58_6] (fun x hx => ab_bits hx) qcov_58 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_58_0, qch_58_1, qch_58_2, qch_58_3, qch_58_4, qch_58_5, qch_58_6])

theorem qroot_59 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 59) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_59_0, decode 300 e_59_1, decode 300 e_59_2, decode 300 e_59_3, decode 300 e_59_4, decode 300 e_59_5, decode 174 e_59_6] (fun x hx => ab_bits hx) qcov_59 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_59_0, qch_59_1, qch_59_2, qch_59_3, qch_59_4, qch_59_5, qch_59_6])

theorem qroot_60 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 60) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_60_0, decode 300 e_60_1, decode 300 e_60_2, decode 300 e_60_3, decode 300 e_60_4, decode 300 e_60_5, decode 174 e_60_6] (fun x hx => ab_bits hx) qcov_60 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_60_0, qch_60_1, qch_60_2, qch_60_3, qch_60_4, qch_60_5, qch_60_6])

theorem qroot_61 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 61) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_61_0, decode 300 e_61_1, decode 300 e_61_2, decode 300 e_61_3, decode 300 e_61_4, decode 300 e_61_5, decode 174 e_61_6] (fun x hx => ab_bits hx) qcov_61 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_61_0, qch_61_1, qch_61_2, qch_61_3, qch_61_4, qch_61_5, qch_61_6])

theorem qroot_62 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 62) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_62_0, decode 300 e_62_1, decode 300 e_62_2, decode 300 e_62_3, decode 300 e_62_4, decode 300 e_62_5, decode 174 e_62_6] (fun x hx => ab_bits hx) qcov_62 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_62_0, qch_62_1, qch_62_2, qch_62_3, qch_62_4, qch_62_5, qch_62_6])

theorem qroot_63 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 63) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_63_0, decode 300 e_63_1, decode 300 e_63_2, decode 300 e_63_3, decode 300 e_63_4, decode 300 e_63_5, decode 174 e_63_6] (fun x hx => ab_bits hx) qcov_63 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_63_0, qch_63_1, qch_63_2, qch_63_3, qch_63_4, qch_63_5, qch_63_6])

theorem qroot_64 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 64) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_64_0, decode 300 e_64_1, decode 300 e_64_2, decode 300 e_64_3, decode 300 e_64_4, decode 300 e_64_5, decode 174 e_64_6] (fun x hx => ab_bits hx) qcov_64 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_64_0, qch_64_1, qch_64_2, qch_64_3, qch_64_4, qch_64_5, qch_64_6])

theorem qroot_65 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 65) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_65_0, decode 300 e_65_1, decode 300 e_65_2, decode 300 e_65_3, decode 300 e_65_4, decode 300 e_65_5, decode 174 e_65_6] (fun x hx => ab_bits hx) qcov_65 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_65_0, qch_65_1, qch_65_2, qch_65_3, qch_65_4, qch_65_5, qch_65_6])

theorem qroot_66 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 66) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_66_0, decode 300 e_66_1, decode 300 e_66_2, decode 300 e_66_3, decode 300 e_66_4, decode 300 e_66_5, decode 174 e_66_6] (fun x hx => ab_bits hx) qcov_66 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_66_0, qch_66_1, qch_66_2, qch_66_3, qch_66_4, qch_66_5, qch_66_6])

theorem qroot_67 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 67) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_67_0, decode 300 e_67_1, decode 300 e_67_2, decode 300 e_67_3, decode 300 e_67_4, decode 300 e_67_5, decode 174 e_67_6] (fun x hx => ab_bits hx) qcov_67 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_67_0, qch_67_1, qch_67_2, qch_67_3, qch_67_4, qch_67_5, qch_67_6])

theorem qroot_68 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 68) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_68_0, decode 300 e_68_1, decode 300 e_68_2, decode 300 e_68_3, decode 300 e_68_4, decode 300 e_68_5, decode 174 e_68_6] (fun x hx => ab_bits hx) qcov_68 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_68_0, qch_68_1, qch_68_2, qch_68_3, qch_68_4, qch_68_5, qch_68_6])

theorem qroot_69 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 69) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_69_0, decode 300 e_69_1, decode 300 e_69_2, decode 300 e_69_3, decode 300 e_69_4, decode 300 e_69_5, decode 174 e_69_6] (fun x hx => ab_bits hx) qcov_69 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_69_0, qch_69_1, qch_69_2, qch_69_3, qch_69_4, qch_69_5, qch_69_6])

theorem qroot_70 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 70) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_70_0, decode 300 e_70_1, decode 300 e_70_2, decode 300 e_70_3, decode 300 e_70_4, decode 300 e_70_5, decode 174 e_70_6] (fun x hx => ab_bits hx) qcov_70 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_70_0, qch_70_1, qch_70_2, qch_70_3, qch_70_4, qch_70_5, qch_70_6])

theorem qroot_71 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 71) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_71_0, decode 300 e_71_1, decode 300 e_71_2, decode 300 e_71_3, decode 300 e_71_4, decode 300 e_71_5, decode 174 e_71_6] (fun x hx => ab_bits hx) qcov_71 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_71_0, qch_71_1, qch_71_2, qch_71_3, qch_71_4, qch_71_5, qch_71_6])

theorem qroot_72 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 72) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_72_0, decode 300 e_72_1, decode 300 e_72_2, decode 300 e_72_3, decode 300 e_72_4, decode 300 e_72_5, decode 174 e_72_6] (fun x hx => ab_bits hx) qcov_72 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_72_0, qch_72_1, qch_72_2, qch_72_3, qch_72_4, qch_72_5, qch_72_6])

theorem qroot_73 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 73) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_73_0, decode 300 e_73_1, decode 300 e_73_2, decode 300 e_73_3, decode 300 e_73_4, decode 300 e_73_5, decode 174 e_73_6] (fun x hx => ab_bits hx) qcov_73 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_73_0, qch_73_1, qch_73_2, qch_73_3, qch_73_4, qch_73_5, qch_73_6])

theorem qroot_74 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 74) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_74_0, decode 300 e_74_1, decode 300 e_74_2, decode 300 e_74_3, decode 300 e_74_4, decode 300 e_74_5, decode 174 e_74_6] (fun x hx => ab_bits hx) qcov_74 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_74_0, qch_74_1, qch_74_2, qch_74_3, qch_74_4, qch_74_5, qch_74_6])

theorem qroot_75 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 75) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_75_0, decode 300 e_75_1, decode 300 e_75_2, decode 300 e_75_3, decode 300 e_75_4, decode 300 e_75_5, decode 174 e_75_6] (fun x hx => ab_bits hx) qcov_75 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_75_0, qch_75_1, qch_75_2, qch_75_3, qch_75_4, qch_75_5, qch_75_6])

theorem qroot_76 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 76) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_76_0, decode 300 e_76_1, decode 300 e_76_2, decode 300 e_76_3, decode 300 e_76_4, decode 300 e_76_5, decode 174 e_76_6] (fun x hx => ab_bits hx) qcov_76 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_76_0, qch_76_1, qch_76_2, qch_76_3, qch_76_4, qch_76_5, qch_76_6])

theorem qroot_77 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 77) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_77_0, decode 300 e_77_1, decode 300 e_77_2, decode 300 e_77_3, decode 300 e_77_4, decode 300 e_77_5, decode 174 e_77_6] (fun x hx => ab_bits hx) qcov_77 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_77_0, qch_77_1, qch_77_2, qch_77_3, qch_77_4, qch_77_5, qch_77_6])

theorem qroot_78 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 78) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_78_0, decode 300 e_78_1, decode 300 e_78_2, decode 300 e_78_3, decode 300 e_78_4, decode 300 e_78_5, decode 174 e_78_6] (fun x hx => ab_bits hx) qcov_78 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_78_0, qch_78_1, qch_78_2, qch_78_3, qch_78_4, qch_78_5, qch_78_6])

theorem qroot_79 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 79) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_79_0, decode 300 e_79_1, decode 300 e_79_2, decode 300 e_79_3, decode 300 e_79_4, decode 300 e_79_5, decode 174 e_79_6] (fun x hx => ab_bits hx) qcov_79 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_79_0, qch_79_1, qch_79_2, qch_79_3, qch_79_4, qch_79_5, qch_79_6])

theorem qroot_80 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 80) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_80_0, decode 300 e_80_1, decode 300 e_80_2, decode 300 e_80_3, decode 300 e_80_4, decode 300 e_80_5, decode 174 e_80_6] (fun x hx => ab_bits hx) qcov_80 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_80_0, qch_80_1, qch_80_2, qch_80_3, qch_80_4, qch_80_5, qch_80_6])

theorem qroot_81 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 81) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_81_0, decode 300 e_81_1, decode 300 e_81_2, decode 300 e_81_3, decode 300 e_81_4, decode 300 e_81_5, decode 174 e_81_6] (fun x hx => ab_bits hx) qcov_81 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_81_0, qch_81_1, qch_81_2, qch_81_3, qch_81_4, qch_81_5, qch_81_6])

theorem qroot_82 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 82) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_82_0, decode 300 e_82_1, decode 300 e_82_2, decode 300 e_82_3, decode 300 e_82_4, decode 300 e_82_5, decode 174 e_82_6] (fun x hx => ab_bits hx) qcov_82 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_82_0, qch_82_1, qch_82_2, qch_82_3, qch_82_4, qch_82_5, qch_82_6])

theorem qroot_83 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 83) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_83_0, decode 300 e_83_1, decode 300 e_83_2, decode 300 e_83_3, decode 300 e_83_4, decode 300 e_83_5, decode 174 e_83_6] (fun x hx => ab_bits hx) qcov_83 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_83_0, qch_83_1, qch_83_2, qch_83_3, qch_83_4, qch_83_5, qch_83_6])

theorem qroot_84 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 84) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_84_0, decode 300 e_84_1, decode 300 e_84_2, decode 300 e_84_3, decode 300 e_84_4, decode 300 e_84_5, decode 177 e_84_6] (fun x hx => ab_bits hx) qcov_84 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_84_0, qch_84_1, qch_84_2, qch_84_3, qch_84_4, qch_84_5, qch_84_6])

theorem qroot_85 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 85) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_85_0, decode 300 e_85_1, decode 300 e_85_2, decode 300 e_85_3, decode 300 e_85_4, decode 300 e_85_5, decode 177 e_85_6] (fun x hx => ab_bits hx) qcov_85 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_85_0, qch_85_1, qch_85_2, qch_85_3, qch_85_4, qch_85_5, qch_85_6])

theorem qroot_86 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 86) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_86_0, decode 300 e_86_1, decode 300 e_86_2, decode 300 e_86_3, decode 300 e_86_4, decode 300 e_86_5, decode 177 e_86_6] (fun x hx => ab_bits hx) qcov_86 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_86_0, qch_86_1, qch_86_2, qch_86_3, qch_86_4, qch_86_5, qch_86_6])

theorem qroot_87 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 87) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_87_0, decode 300 e_87_1, decode 300 e_87_2, decode 300 e_87_3, decode 300 e_87_4, decode 300 e_87_5, decode 177 e_87_6] (fun x hx => ab_bits hx) qcov_87 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_87_0, qch_87_1, qch_87_2, qch_87_3, qch_87_4, qch_87_5, qch_87_6])

theorem qroot_88 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 88) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_88_0, decode 300 e_88_1, decode 300 e_88_2, decode 300 e_88_3, decode 300 e_88_4, decode 300 e_88_5, decode 177 e_88_6] (fun x hx => ab_bits hx) qcov_88 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_88_0, qch_88_1, qch_88_2, qch_88_3, qch_88_4, qch_88_5, qch_88_6])

theorem qroot_89 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 89) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_89_0, decode 300 e_89_1, decode 300 e_89_2, decode 300 e_89_3, decode 300 e_89_4, decode 300 e_89_5, decode 177 e_89_6] (fun x hx => ab_bits hx) qcov_89 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_89_0, qch_89_1, qch_89_2, qch_89_3, qch_89_4, qch_89_5, qch_89_6])

theorem qroot_90 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 90) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_90_0, decode 300 e_90_1, decode 300 e_90_2, decode 300 e_90_3, decode 300 e_90_4, decode 300 e_90_5, decode 177 e_90_6] (fun x hx => ab_bits hx) qcov_90 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_90_0, qch_90_1, qch_90_2, qch_90_3, qch_90_4, qch_90_5, qch_90_6])

theorem qroot_91 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 91) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_91_0, decode 300 e_91_1, decode 300 e_91_2, decode 300 e_91_3, decode 300 e_91_4, decode 300 e_91_5, decode 177 e_91_6] (fun x hx => ab_bits hx) qcov_91 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_91_0, qch_91_1, qch_91_2, qch_91_3, qch_91_4, qch_91_5, qch_91_6])

theorem qroot_92 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 92) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_92_0, decode 300 e_92_1, decode 300 e_92_2, decode 300 e_92_3, decode 300 e_92_4, decode 300 e_92_5, decode 177 e_92_6] (fun x hx => ab_bits hx) qcov_92 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_92_0, qch_92_1, qch_92_2, qch_92_3, qch_92_4, qch_92_5, qch_92_6])

theorem qroot_93 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 93) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_93_0, decode 300 e_93_1, decode 300 e_93_2, decode 300 e_93_3, decode 300 e_93_4, decode 300 e_93_5, decode 177 e_93_6] (fun x hx => ab_bits hx) qcov_93 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_93_0, qch_93_1, qch_93_2, qch_93_3, qch_93_4, qch_93_5, qch_93_6])

theorem qroot_94 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 94) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_94_0, decode 300 e_94_1, decode 300 e_94_2, decode 300 e_94_3, decode 300 e_94_4, decode 300 e_94_5, decode 177 e_94_6] (fun x hx => ab_bits hx) qcov_94 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_94_0, qch_94_1, qch_94_2, qch_94_3, qch_94_4, qch_94_5, qch_94_6])

theorem qroot_95 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 95) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_95_0, decode 300 e_95_1, decode 300 e_95_2, decode 300 e_95_3, decode 300 e_95_4, decode 300 e_95_5, decode 177 e_95_6] (fun x hx => ab_bits hx) qcov_95 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_95_0, qch_95_1, qch_95_2, qch_95_3, qch_95_4, qch_95_5, qch_95_6])

theorem qroot_96 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 96) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_96_0, decode 300 e_96_1, decode 300 e_96_2, decode 300 e_96_3, decode 300 e_96_4, decode 300 e_96_5, decode 177 e_96_6] (fun x hx => ab_bits hx) qcov_96 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_96_0, qch_96_1, qch_96_2, qch_96_3, qch_96_4, qch_96_5, qch_96_6])

theorem qroot_97 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 97) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_97_0, decode 300 e_97_1, decode 300 e_97_2, decode 300 e_97_3, decode 300 e_97_4, decode 300 e_97_5, decode 177 e_97_6] (fun x hx => ab_bits hx) qcov_97 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_97_0, qch_97_1, qch_97_2, qch_97_3, qch_97_4, qch_97_5, qch_97_6])

theorem qroot_98 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 98) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_98_0, decode 300 e_98_1, decode 300 e_98_2, decode 300 e_98_3, decode 300 e_98_4, decode 300 e_98_5, decode 177 e_98_6] (fun x hx => ab_bits hx) qcov_98 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_98_0, qch_98_1, qch_98_2, qch_98_3, qch_98_4, qch_98_5, qch_98_6])

theorem qroot_99 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 99) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_99_0, decode 300 e_99_1, decode 300 e_99_2, decode 300 e_99_3, decode 300 e_99_4, decode 300 e_99_5, decode 177 e_99_6] (fun x hx => ab_bits hx) qcov_99 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_99_0, qch_99_1, qch_99_2, qch_99_3, qch_99_4, qch_99_5, qch_99_6])

theorem qroot_100 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 100) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_100_0, decode 300 e_100_1, decode 300 e_100_2, decode 300 e_100_3, decode 300 e_100_4, decode 300 e_100_5, decode 177 e_100_6] (fun x hx => ab_bits hx) qcov_100 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_100_0, qch_100_1, qch_100_2, qch_100_3, qch_100_4, qch_100_5, qch_100_6])

theorem qroot_101 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 101) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_101_0, decode 300 e_101_1, decode 300 e_101_2, decode 300 e_101_3, decode 300 e_101_4, decode 300 e_101_5, decode 177 e_101_6] (fun x hx => ab_bits hx) qcov_101 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_101_0, qch_101_1, qch_101_2, qch_101_3, qch_101_4, qch_101_5, qch_101_6])

theorem qroot_102 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 102) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_102_0, decode 300 e_102_1, decode 300 e_102_2, decode 300 e_102_3, decode 300 e_102_4, decode 300 e_102_5, decode 177 e_102_6] (fun x hx => ab_bits hx) qcov_102 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_102_0, qch_102_1, qch_102_2, qch_102_3, qch_102_4, qch_102_5, qch_102_6])

theorem qroot_103 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 103) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_103_0, decode 300 e_103_1, decode 300 e_103_2, decode 300 e_103_3, decode 300 e_103_4, decode 300 e_103_5, decode 177 e_103_6] (fun x hx => ab_bits hx) qcov_103 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_103_0, qch_103_1, qch_103_2, qch_103_3, qch_103_4, qch_103_5, qch_103_6])

theorem qroot_104 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 104) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_104_0, decode 300 e_104_1, decode 300 e_104_2, decode 300 e_104_3, decode 300 e_104_4, decode 300 e_104_5, decode 177 e_104_6] (fun x hx => ab_bits hx) qcov_104 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_104_0, qch_104_1, qch_104_2, qch_104_3, qch_104_4, qch_104_5, qch_104_6])

theorem qroot_105 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 105) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_105_0, decode 300 e_105_1, decode 300 e_105_2, decode 300 e_105_3, decode 300 e_105_4, decode 300 e_105_5, decode 177 e_105_6] (fun x hx => ab_bits hx) qcov_105 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_105_0, qch_105_1, qch_105_2, qch_105_3, qch_105_4, qch_105_5, qch_105_6])

theorem qroot_106 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 106) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_106_0, decode 300 e_106_1, decode 300 e_106_2, decode 300 e_106_3, decode 300 e_106_4, decode 300 e_106_5, decode 177 e_106_6] (fun x hx => ab_bits hx) qcov_106 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_106_0, qch_106_1, qch_106_2, qch_106_3, qch_106_4, qch_106_5, qch_106_6])

theorem qroot_107 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 107) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_107_0, decode 300 e_107_1, decode 300 e_107_2, decode 300 e_107_3, decode 300 e_107_4, decode 300 e_107_5, decode 177 e_107_6] (fun x hx => ab_bits hx) qcov_107 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_107_0, qch_107_1, qch_107_2, qch_107_3, qch_107_4, qch_107_5, qch_107_6])

theorem qroot_108 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 108) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_108_0, decode 300 e_108_1, decode 300 e_108_2, decode 300 e_108_3, decode 300 e_108_4, decode 300 e_108_5, decode 177 e_108_6] (fun x hx => ab_bits hx) qcov_108 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_108_0, qch_108_1, qch_108_2, qch_108_3, qch_108_4, qch_108_5, qch_108_6])

theorem qroot_109 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 109) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_109_0, decode 300 e_109_1, decode 300 e_109_2, decode 300 e_109_3, decode 300 e_109_4, decode 300 e_109_5, decode 177 e_109_6] (fun x hx => ab_bits hx) qcov_109 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_109_0, qch_109_1, qch_109_2, qch_109_3, qch_109_4, qch_109_5, qch_109_6])

theorem qroot_110 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 110) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_110_0, decode 300 e_110_1, decode 300 e_110_2, decode 300 e_110_3, decode 300 e_110_4, decode 300 e_110_5, decode 177 e_110_6] (fun x hx => ab_bits hx) qcov_110 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_110_0, qch_110_1, qch_110_2, qch_110_3, qch_110_4, qch_110_5, qch_110_6])

theorem qroot_111 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 111) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_111_0, decode 300 e_111_1, decode 300 e_111_2, decode 300 e_111_3, decode 300 e_111_4, decode 300 e_111_5, decode 177 e_111_6] (fun x hx => ab_bits hx) qcov_111 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_111_0, qch_111_1, qch_111_2, qch_111_3, qch_111_4, qch_111_5, qch_111_6])

theorem qroot_112 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 112) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_112_0, decode 300 e_112_1, decode 300 e_112_2, decode 300 e_112_3, decode 300 e_112_4, decode 300 e_112_5, decode 177 e_112_6] (fun x hx => ab_bits hx) qcov_112 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_112_0, qch_112_1, qch_112_2, qch_112_3, qch_112_4, qch_112_5, qch_112_6])

theorem qroot_113 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 113) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_113_0, decode 300 e_113_1, decode 300 e_113_2, decode 300 e_113_3, decode 300 e_113_4, decode 300 e_113_5, decode 177 e_113_6] (fun x hx => ab_bits hx) qcov_113 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_113_0, qch_113_1, qch_113_2, qch_113_3, qch_113_4, qch_113_5, qch_113_6])

theorem qroot_114 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 114) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_114_0, decode 300 e_114_1, decode 300 e_114_2, decode 300 e_114_3, decode 300 e_114_4, decode 300 e_114_5, decode 177 e_114_6] (fun x hx => ab_bits hx) qcov_114 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_114_0, qch_114_1, qch_114_2, qch_114_3, qch_114_4, qch_114_5, qch_114_6])

theorem qroot_115 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 115) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_115_0, decode 300 e_115_1, decode 300 e_115_2, decode 300 e_115_3, decode 300 e_115_4, decode 300 e_115_5, decode 177 e_115_6] (fun x hx => ab_bits hx) qcov_115 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_115_0, qch_115_1, qch_115_2, qch_115_3, qch_115_4, qch_115_5, qch_115_6])

theorem qroot_116 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 116) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_116_0, decode 300 e_116_1, decode 300 e_116_2, decode 300 e_116_3, decode 300 e_116_4, decode 300 e_116_5, decode 177 e_116_6] (fun x hx => ab_bits hx) qcov_116 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_116_0, qch_116_1, qch_116_2, qch_116_3, qch_116_4, qch_116_5, qch_116_6])

theorem qroot_117 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 117) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_117_0, decode 300 e_117_1, decode 300 e_117_2, decode 300 e_117_3, decode 300 e_117_4, decode 300 e_117_5, decode 177 e_117_6] (fun x hx => ab_bits hx) qcov_117 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_117_0, qch_117_1, qch_117_2, qch_117_3, qch_117_4, qch_117_5, qch_117_6])

theorem qroot_118 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 118) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_118_0, decode 300 e_118_1, decode 300 e_118_2, decode 300 e_118_3, decode 300 e_118_4, decode 300 e_118_5, decode 177 e_118_6] (fun x hx => ab_bits hx) qcov_118 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_118_0, qch_118_1, qch_118_2, qch_118_3, qch_118_4, qch_118_5, qch_118_6])

theorem qroot_119 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 119) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_119_0, decode 300 e_119_1, decode 300 e_119_2, decode 300 e_119_3, decode 300 e_119_4, decode 300 e_119_5, decode 177 e_119_6] (fun x hx => ab_bits hx) qcov_119 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_119_0, qch_119_1, qch_119_2, qch_119_3, qch_119_4, qch_119_5, qch_119_6])

theorem qroot_120 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 120) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_120_0, decode 300 e_120_1, decode 300 e_120_2, decode 300 e_120_3, decode 300 e_120_4, decode 300 e_120_5, decode 177 e_120_6] (fun x hx => ab_bits hx) qcov_120 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_120_0, qch_120_1, qch_120_2, qch_120_3, qch_120_4, qch_120_5, qch_120_6])

theorem qroot_121 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 121) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_121_0, decode 300 e_121_1, decode 300 e_121_2, decode 300 e_121_3, decode 300 e_121_4, decode 300 e_121_5, decode 177 e_121_6] (fun x hx => ab_bits hx) qcov_121 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_121_0, qch_121_1, qch_121_2, qch_121_3, qch_121_4, qch_121_5, qch_121_6])

theorem qroot_122 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 122) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_122_0, decode 300 e_122_1, decode 300 e_122_2, decode 300 e_122_3, decode 300 e_122_4, decode 300 e_122_5, decode 177 e_122_6] (fun x hx => ab_bits hx) qcov_122 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_122_0, qch_122_1, qch_122_2, qch_122_3, qch_122_4, qch_122_5, qch_122_6])

theorem qroot_123 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 123) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_123_0, decode 300 e_123_1, decode 300 e_123_2, decode 300 e_123_3, decode 300 e_123_4, decode 300 e_123_5, decode 177 e_123_6] (fun x hx => ab_bits hx) qcov_123 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_123_0, qch_123_1, qch_123_2, qch_123_3, qch_123_4, qch_123_5, qch_123_6])

theorem qroot_124 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 124) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_124_0, decode 300 e_124_1, decode 300 e_124_2, decode 300 e_124_3, decode 300 e_124_4, decode 300 e_124_5, decode 177 e_124_6] (fun x hx => ab_bits hx) qcov_124 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_124_0, qch_124_1, qch_124_2, qch_124_3, qch_124_4, qch_124_5, qch_124_6])

theorem qroot_125 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 125) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_125_0, decode 300 e_125_1, decode 300 e_125_2, decode 300 e_125_3, decode 300 e_125_4, decode 300 e_125_5, decode 177 e_125_6] (fun x hx => ab_bits hx) qcov_125 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_125_0, qch_125_1, qch_125_2, qch_125_3, qch_125_4, qch_125_5, qch_125_6])

theorem qroot_126 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 126) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_126_0, decode 300 e_126_1, decode 300 e_126_2, decode 300 e_126_3, decode 300 e_126_4, decode 300 e_126_5, decode 175 e_126_6] (fun x hx => ab_bits hx) qcov_126 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_126_0, qch_126_1, qch_126_2, qch_126_3, qch_126_4, qch_126_5, qch_126_6])

theorem qroot_127 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 127) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_127_0, decode 300 e_127_1, decode 300 e_127_2, decode 300 e_127_3, decode 300 e_127_4, decode 300 e_127_5, decode 175 e_127_6] (fun x hx => ab_bits hx) qcov_127 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_127_0, qch_127_1, qch_127_2, qch_127_3, qch_127_4, qch_127_5, qch_127_6])

theorem qroot_128 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 128) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_128_0, decode 300 e_128_1, decode 300 e_128_2, decode 300 e_128_3, decode 300 e_128_4, decode 300 e_128_5, decode 175 e_128_6] (fun x hx => ab_bits hx) qcov_128 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_128_0, qch_128_1, qch_128_2, qch_128_3, qch_128_4, qch_128_5, qch_128_6])

theorem qroot_129 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 129) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_129_0, decode 300 e_129_1, decode 300 e_129_2, decode 300 e_129_3, decode 300 e_129_4, decode 300 e_129_5, decode 175 e_129_6] (fun x hx => ab_bits hx) qcov_129 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_129_0, qch_129_1, qch_129_2, qch_129_3, qch_129_4, qch_129_5, qch_129_6])

theorem qroot_130 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 130) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_130_0, decode 300 e_130_1, decode 300 e_130_2, decode 300 e_130_3, decode 300 e_130_4, decode 300 e_130_5, decode 175 e_130_6] (fun x hx => ab_bits hx) qcov_130 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_130_0, qch_130_1, qch_130_2, qch_130_3, qch_130_4, qch_130_5, qch_130_6])

theorem qroot_131 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 131) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_131_0, decode 300 e_131_1, decode 300 e_131_2, decode 300 e_131_3, decode 300 e_131_4, decode 300 e_131_5, decode 175 e_131_6] (fun x hx => ab_bits hx) qcov_131 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_131_0, qch_131_1, qch_131_2, qch_131_3, qch_131_4, qch_131_5, qch_131_6])

theorem qroot_132 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 132) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_132_0, decode 300 e_132_1, decode 300 e_132_2, decode 300 e_132_3, decode 300 e_132_4, decode 300 e_132_5, decode 175 e_132_6] (fun x hx => ab_bits hx) qcov_132 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_132_0, qch_132_1, qch_132_2, qch_132_3, qch_132_4, qch_132_5, qch_132_6])

theorem qroot_133 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 133) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_133_0, decode 300 e_133_1, decode 300 e_133_2, decode 300 e_133_3, decode 300 e_133_4, decode 300 e_133_5, decode 175 e_133_6] (fun x hx => ab_bits hx) qcov_133 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_133_0, qch_133_1, qch_133_2, qch_133_3, qch_133_4, qch_133_5, qch_133_6])

theorem qroot_134 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 134) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_134_0, decode 300 e_134_1, decode 300 e_134_2, decode 300 e_134_3, decode 300 e_134_4, decode 300 e_134_5, decode 175 e_134_6] (fun x hx => ab_bits hx) qcov_134 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_134_0, qch_134_1, qch_134_2, qch_134_3, qch_134_4, qch_134_5, qch_134_6])

theorem qroot_135 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 135) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_135_0, decode 300 e_135_1, decode 300 e_135_2, decode 300 e_135_3, decode 300 e_135_4, decode 300 e_135_5, decode 175 e_135_6] (fun x hx => ab_bits hx) qcov_135 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_135_0, qch_135_1, qch_135_2, qch_135_3, qch_135_4, qch_135_5, qch_135_6])

theorem qroot_136 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 136) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_136_0, decode 300 e_136_1, decode 300 e_136_2, decode 300 e_136_3, decode 300 e_136_4, decode 300 e_136_5, decode 175 e_136_6] (fun x hx => ab_bits hx) qcov_136 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_136_0, qch_136_1, qch_136_2, qch_136_3, qch_136_4, qch_136_5, qch_136_6])

theorem qroot_137 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 137) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_137_0, decode 300 e_137_1, decode 300 e_137_2, decode 300 e_137_3, decode 300 e_137_4, decode 300 e_137_5, decode 175 e_137_6] (fun x hx => ab_bits hx) qcov_137 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_137_0, qch_137_1, qch_137_2, qch_137_3, qch_137_4, qch_137_5, qch_137_6])

theorem qroot_138 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 138) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_138_0, decode 300 e_138_1, decode 300 e_138_2, decode 300 e_138_3, decode 300 e_138_4, decode 300 e_138_5, decode 175 e_138_6] (fun x hx => ab_bits hx) qcov_138 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_138_0, qch_138_1, qch_138_2, qch_138_3, qch_138_4, qch_138_5, qch_138_6])

theorem qroot_139 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 139) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_139_0, decode 300 e_139_1, decode 300 e_139_2, decode 300 e_139_3, decode 300 e_139_4, decode 300 e_139_5, decode 175 e_139_6] (fun x hx => ab_bits hx) qcov_139 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_139_0, qch_139_1, qch_139_2, qch_139_3, qch_139_4, qch_139_5, qch_139_6])

theorem qroot_140 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 140) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_140_0, decode 300 e_140_1, decode 300 e_140_2, decode 300 e_140_3, decode 300 e_140_4, decode 300 e_140_5, decode 175 e_140_6] (fun x hx => ab_bits hx) qcov_140 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_140_0, qch_140_1, qch_140_2, qch_140_3, qch_140_4, qch_140_5, qch_140_6])

theorem qroot_141 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 141) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_141_0, decode 300 e_141_1, decode 300 e_141_2, decode 300 e_141_3, decode 300 e_141_4, decode 300 e_141_5, decode 175 e_141_6] (fun x hx => ab_bits hx) qcov_141 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_141_0, qch_141_1, qch_141_2, qch_141_3, qch_141_4, qch_141_5, qch_141_6])

theorem qroot_142 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 142) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_142_0, decode 300 e_142_1, decode 300 e_142_2, decode 300 e_142_3, decode 300 e_142_4, decode 300 e_142_5, decode 175 e_142_6] (fun x hx => ab_bits hx) qcov_142 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_142_0, qch_142_1, qch_142_2, qch_142_3, qch_142_4, qch_142_5, qch_142_6])

theorem qroot_143 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 143) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_143_0, decode 300 e_143_1, decode 300 e_143_2, decode 300 e_143_3, decode 300 e_143_4, decode 300 e_143_5, decode 175 e_143_6] (fun x hx => ab_bits hx) qcov_143 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_143_0, qch_143_1, qch_143_2, qch_143_3, qch_143_4, qch_143_5, qch_143_6])

theorem qroot_144 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 144) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_144_0, decode 300 e_144_1, decode 300 e_144_2, decode 300 e_144_3, decode 300 e_144_4, decode 300 e_144_5, decode 175 e_144_6] (fun x hx => ab_bits hx) qcov_144 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_144_0, qch_144_1, qch_144_2, qch_144_3, qch_144_4, qch_144_5, qch_144_6])

theorem qroot_145 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 145) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_145_0, decode 300 e_145_1, decode 300 e_145_2, decode 300 e_145_3, decode 300 e_145_4, decode 300 e_145_5, decode 175 e_145_6] (fun x hx => ab_bits hx) qcov_145 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_145_0, qch_145_1, qch_145_2, qch_145_3, qch_145_4, qch_145_5, qch_145_6])

theorem qroot_146 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 146) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_146_0, decode 300 e_146_1, decode 300 e_146_2, decode 300 e_146_3, decode 300 e_146_4, decode 300 e_146_5, decode 175 e_146_6] (fun x hx => ab_bits hx) qcov_146 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_146_0, qch_146_1, qch_146_2, qch_146_3, qch_146_4, qch_146_5, qch_146_6])

theorem qroot_147 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 147) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_147_0, decode 300 e_147_1, decode 300 e_147_2, decode 300 e_147_3, decode 300 e_147_4, decode 300 e_147_5, decode 175 e_147_6] (fun x hx => ab_bits hx) qcov_147 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_147_0, qch_147_1, qch_147_2, qch_147_3, qch_147_4, qch_147_5, qch_147_6])

theorem qroot_148 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 148) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_148_0, decode 300 e_148_1, decode 300 e_148_2, decode 300 e_148_3, decode 300 e_148_4, decode 300 e_148_5, decode 175 e_148_6] (fun x hx => ab_bits hx) qcov_148 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_148_0, qch_148_1, qch_148_2, qch_148_3, qch_148_4, qch_148_5, qch_148_6])

theorem qroot_149 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 149) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_149_0, decode 300 e_149_1, decode 300 e_149_2, decode 300 e_149_3, decode 300 e_149_4, decode 300 e_149_5, decode 175 e_149_6] (fun x hx => ab_bits hx) qcov_149 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_149_0, qch_149_1, qch_149_2, qch_149_3, qch_149_4, qch_149_5, qch_149_6])

theorem qroot_150 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 150) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_150_0, decode 300 e_150_1, decode 300 e_150_2, decode 300 e_150_3, decode 300 e_150_4, decode 300 e_150_5, decode 175 e_150_6] (fun x hx => ab_bits hx) qcov_150 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_150_0, qch_150_1, qch_150_2, qch_150_3, qch_150_4, qch_150_5, qch_150_6])

theorem qroot_151 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 151) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_151_0, decode 300 e_151_1, decode 300 e_151_2, decode 300 e_151_3, decode 300 e_151_4, decode 300 e_151_5, decode 175 e_151_6] (fun x hx => ab_bits hx) qcov_151 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_151_0, qch_151_1, qch_151_2, qch_151_3, qch_151_4, qch_151_5, qch_151_6])

theorem qroot_152 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 152) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_152_0, decode 300 e_152_1, decode 300 e_152_2, decode 300 e_152_3, decode 300 e_152_4, decode 300 e_152_5, decode 175 e_152_6] (fun x hx => ab_bits hx) qcov_152 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_152_0, qch_152_1, qch_152_2, qch_152_3, qch_152_4, qch_152_5, qch_152_6])

theorem qroot_153 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 153) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_153_0, decode 300 e_153_1, decode 300 e_153_2, decode 300 e_153_3, decode 300 e_153_4, decode 300 e_153_5, decode 175 e_153_6] (fun x hx => ab_bits hx) qcov_153 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_153_0, qch_153_1, qch_153_2, qch_153_3, qch_153_4, qch_153_5, qch_153_6])

theorem qroot_154 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 154) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_154_0, decode 300 e_154_1, decode 300 e_154_2, decode 300 e_154_3, decode 300 e_154_4, decode 300 e_154_5, decode 175 e_154_6] (fun x hx => ab_bits hx) qcov_154 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_154_0, qch_154_1, qch_154_2, qch_154_3, qch_154_4, qch_154_5, qch_154_6])

theorem qroot_155 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 155) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_155_0, decode 300 e_155_1, decode 300 e_155_2, decode 300 e_155_3, decode 300 e_155_4, decode 300 e_155_5, decode 175 e_155_6] (fun x hx => ab_bits hx) qcov_155 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_155_0, qch_155_1, qch_155_2, qch_155_3, qch_155_4, qch_155_5, qch_155_6])

theorem qroot_156 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 156) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_156_0, decode 300 e_156_1, decode 300 e_156_2, decode 300 e_156_3, decode 300 e_156_4, decode 300 e_156_5, decode 175 e_156_6] (fun x hx => ab_bits hx) qcov_156 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_156_0, qch_156_1, qch_156_2, qch_156_3, qch_156_4, qch_156_5, qch_156_6])

theorem qroot_157 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 157) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_157_0, decode 300 e_157_1, decode 300 e_157_2, decode 300 e_157_3, decode 300 e_157_4, decode 300 e_157_5, decode 175 e_157_6] (fun x hx => ab_bits hx) qcov_157 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_157_0, qch_157_1, qch_157_2, qch_157_3, qch_157_4, qch_157_5, qch_157_6])

theorem qroot_158 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 158) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_158_0, decode 300 e_158_1, decode 300 e_158_2, decode 300 e_158_3, decode 300 e_158_4, decode 300 e_158_5, decode 175 e_158_6] (fun x hx => ab_bits hx) qcov_158 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_158_0, qch_158_1, qch_158_2, qch_158_3, qch_158_4, qch_158_5, qch_158_6])

theorem qroot_159 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 159) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_159_0, decode 300 e_159_1, decode 300 e_159_2, decode 300 e_159_3, decode 300 e_159_4, decode 300 e_159_5, decode 175 e_159_6] (fun x hx => ab_bits hx) qcov_159 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_159_0, qch_159_1, qch_159_2, qch_159_3, qch_159_4, qch_159_5, qch_159_6])

theorem qroot_160 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 160) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_160_0, decode 300 e_160_1, decode 300 e_160_2, decode 300 e_160_3, decode 300 e_160_4, decode 300 e_160_5, decode 175 e_160_6] (fun x hx => ab_bits hx) qcov_160 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_160_0, qch_160_1, qch_160_2, qch_160_3, qch_160_4, qch_160_5, qch_160_6])

theorem qroot_161 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 161) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_161_0, decode 300 e_161_1, decode 300 e_161_2, decode 300 e_161_3, decode 300 e_161_4, decode 300 e_161_5, decode 175 e_161_6] (fun x hx => ab_bits hx) qcov_161 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_161_0, qch_161_1, qch_161_2, qch_161_3, qch_161_4, qch_161_5, qch_161_6])

theorem qroot_162 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 162) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_162_0, decode 300 e_162_1, decode 300 e_162_2, decode 300 e_162_3, decode 300 e_162_4, decode 300 e_162_5, decode 175 e_162_6] (fun x hx => ab_bits hx) qcov_162 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_162_0, qch_162_1, qch_162_2, qch_162_3, qch_162_4, qch_162_5, qch_162_6])

theorem qroot_163 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 163) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_163_0, decode 300 e_163_1, decode 300 e_163_2, decode 300 e_163_3, decode 300 e_163_4, decode 300 e_163_5, decode 175 e_163_6] (fun x hx => ab_bits hx) qcov_163 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_163_0, qch_163_1, qch_163_2, qch_163_3, qch_163_4, qch_163_5, qch_163_6])

theorem qroot_164 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 164) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_164_0, decode 300 e_164_1, decode 300 e_164_2, decode 300 e_164_3, decode 300 e_164_4, decode 300 e_164_5, decode 175 e_164_6] (fun x hx => ab_bits hx) qcov_164 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_164_0, qch_164_1, qch_164_2, qch_164_3, qch_164_4, qch_164_5, qch_164_6])

theorem qroot_165 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 165) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_165_0, decode 300 e_165_1, decode 300 e_165_2, decode 300 e_165_3, decode 300 e_165_4, decode 300 e_165_5, decode 175 e_165_6] (fun x hx => ab_bits hx) qcov_165 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_165_0, qch_165_1, qch_165_2, qch_165_3, qch_165_4, qch_165_5, qch_165_6])

theorem qroot_166 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 166) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_166_0, decode 300 e_166_1, decode 300 e_166_2, decode 300 e_166_3, decode 300 e_166_4, decode 300 e_166_5, decode 175 e_166_6] (fun x hx => ab_bits hx) qcov_166 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_166_0, qch_166_1, qch_166_2, qch_166_3, qch_166_4, qch_166_5, qch_166_6])

theorem qroot_167 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 167) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_167_0, decode 300 e_167_1, decode 300 e_167_2, decode 300 e_167_3, decode 300 e_167_4, decode 300 e_167_5, decode 175 e_167_6] (fun x hx => ab_bits hx) qcov_167 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_167_0, qch_167_1, qch_167_2, qch_167_3, qch_167_4, qch_167_5, qch_167_6])

theorem qroot_168 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 168) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_168_0, decode 300 e_168_1, decode 300 e_168_2, decode 300 e_168_3, decode 300 e_168_4, decode 300 e_168_5, decode 173 e_168_6] (fun x hx => ab_bits hx) qcov_168 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_168_0, qch_168_1, qch_168_2, qch_168_3, qch_168_4, qch_168_5, qch_168_6])

theorem qroot_169 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 169) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_169_0, decode 300 e_169_1, decode 300 e_169_2, decode 300 e_169_3, decode 300 e_169_4, decode 300 e_169_5, decode 173 e_169_6] (fun x hx => ab_bits hx) qcov_169 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_169_0, qch_169_1, qch_169_2, qch_169_3, qch_169_4, qch_169_5, qch_169_6])

theorem qroot_170 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 170) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_170_0, decode 300 e_170_1, decode 300 e_170_2, decode 300 e_170_3, decode 300 e_170_4, decode 300 e_170_5, decode 173 e_170_6] (fun x hx => ab_bits hx) qcov_170 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_170_0, qch_170_1, qch_170_2, qch_170_3, qch_170_4, qch_170_5, qch_170_6])

theorem qroot_171 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 171) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_171_0, decode 300 e_171_1, decode 300 e_171_2, decode 300 e_171_3, decode 300 e_171_4, decode 300 e_171_5, decode 173 e_171_6] (fun x hx => ab_bits hx) qcov_171 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_171_0, qch_171_1, qch_171_2, qch_171_3, qch_171_4, qch_171_5, qch_171_6])

theorem qroot_172 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 172) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_172_0, decode 300 e_172_1, decode 300 e_172_2, decode 300 e_172_3, decode 300 e_172_4, decode 300 e_172_5, decode 173 e_172_6] (fun x hx => ab_bits hx) qcov_172 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_172_0, qch_172_1, qch_172_2, qch_172_3, qch_172_4, qch_172_5, qch_172_6])

theorem qroot_173 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 173) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_173_0, decode 300 e_173_1, decode 300 e_173_2, decode 300 e_173_3, decode 300 e_173_4, decode 300 e_173_5, decode 173 e_173_6] (fun x hx => ab_bits hx) qcov_173 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_173_0, qch_173_1, qch_173_2, qch_173_3, qch_173_4, qch_173_5, qch_173_6])

theorem qroot_174 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 174) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_174_0, decode 300 e_174_1, decode 300 e_174_2, decode 300 e_174_3, decode 300 e_174_4, decode 300 e_174_5, decode 173 e_174_6] (fun x hx => ab_bits hx) qcov_174 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_174_0, qch_174_1, qch_174_2, qch_174_3, qch_174_4, qch_174_5, qch_174_6])

theorem qroot_175 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 175) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_175_0, decode 300 e_175_1, decode 300 e_175_2, decode 300 e_175_3, decode 300 e_175_4, decode 300 e_175_5, decode 173 e_175_6] (fun x hx => ab_bits hx) qcov_175 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_175_0, qch_175_1, qch_175_2, qch_175_3, qch_175_4, qch_175_5, qch_175_6])

theorem qroot_176 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 176) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_176_0, decode 300 e_176_1, decode 300 e_176_2, decode 300 e_176_3, decode 300 e_176_4, decode 300 e_176_5, decode 173 e_176_6] (fun x hx => ab_bits hx) qcov_176 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_176_0, qch_176_1, qch_176_2, qch_176_3, qch_176_4, qch_176_5, qch_176_6])

theorem qroot_177 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 177) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_177_0, decode 300 e_177_1, decode 300 e_177_2, decode 300 e_177_3, decode 300 e_177_4, decode 300 e_177_5, decode 173 e_177_6] (fun x hx => ab_bits hx) qcov_177 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_177_0, qch_177_1, qch_177_2, qch_177_3, qch_177_4, qch_177_5, qch_177_6])

theorem qroot_178 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 178) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_178_0, decode 300 e_178_1, decode 300 e_178_2, decode 300 e_178_3, decode 300 e_178_4, decode 300 e_178_5, decode 173 e_178_6] (fun x hx => ab_bits hx) qcov_178 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_178_0, qch_178_1, qch_178_2, qch_178_3, qch_178_4, qch_178_5, qch_178_6])

theorem qroot_179 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 179) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_179_0, decode 300 e_179_1, decode 300 e_179_2, decode 300 e_179_3, decode 300 e_179_4, decode 300 e_179_5, decode 173 e_179_6] (fun x hx => ab_bits hx) qcov_179 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_179_0, qch_179_1, qch_179_2, qch_179_3, qch_179_4, qch_179_5, qch_179_6])

theorem qroot_180 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 180) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_180_0, decode 300 e_180_1, decode 300 e_180_2, decode 300 e_180_3, decode 300 e_180_4, decode 300 e_180_5, decode 173 e_180_6] (fun x hx => ab_bits hx) qcov_180 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_180_0, qch_180_1, qch_180_2, qch_180_3, qch_180_4, qch_180_5, qch_180_6])

theorem qroot_181 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 181) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_181_0, decode 300 e_181_1, decode 300 e_181_2, decode 300 e_181_3, decode 300 e_181_4, decode 300 e_181_5, decode 173 e_181_6] (fun x hx => ab_bits hx) qcov_181 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_181_0, qch_181_1, qch_181_2, qch_181_3, qch_181_4, qch_181_5, qch_181_6])

theorem qroot_182 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 182) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_182_0, decode 300 e_182_1, decode 300 e_182_2, decode 300 e_182_3, decode 300 e_182_4, decode 300 e_182_5, decode 173 e_182_6] (fun x hx => ab_bits hx) qcov_182 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_182_0, qch_182_1, qch_182_2, qch_182_3, qch_182_4, qch_182_5, qch_182_6])

theorem qroot_183 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 183) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_183_0, decode 300 e_183_1, decode 300 e_183_2, decode 300 e_183_3, decode 300 e_183_4, decode 300 e_183_5, decode 173 e_183_6] (fun x hx => ab_bits hx) qcov_183 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_183_0, qch_183_1, qch_183_2, qch_183_3, qch_183_4, qch_183_5, qch_183_6])

theorem qroot_184 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 184) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_184_0, decode 300 e_184_1, decode 300 e_184_2, decode 300 e_184_3, decode 300 e_184_4, decode 300 e_184_5, decode 173 e_184_6] (fun x hx => ab_bits hx) qcov_184 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_184_0, qch_184_1, qch_184_2, qch_184_3, qch_184_4, qch_184_5, qch_184_6])

theorem qroot_185 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 185) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_185_0, decode 300 e_185_1, decode 300 e_185_2, decode 300 e_185_3, decode 300 e_185_4, decode 300 e_185_5, decode 173 e_185_6] (fun x hx => ab_bits hx) qcov_185 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_185_0, qch_185_1, qch_185_2, qch_185_3, qch_185_4, qch_185_5, qch_185_6])

theorem qroot_186 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 186) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_186_0, decode 300 e_186_1, decode 300 e_186_2, decode 300 e_186_3, decode 300 e_186_4, decode 300 e_186_5, decode 173 e_186_6] (fun x hx => ab_bits hx) qcov_186 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_186_0, qch_186_1, qch_186_2, qch_186_3, qch_186_4, qch_186_5, qch_186_6])

theorem qroot_187 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 187) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_187_0, decode 300 e_187_1, decode 300 e_187_2, decode 300 e_187_3, decode 300 e_187_4, decode 300 e_187_5, decode 173 e_187_6] (fun x hx => ab_bits hx) qcov_187 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_187_0, qch_187_1, qch_187_2, qch_187_3, qch_187_4, qch_187_5, qch_187_6])

theorem qroot_188 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 188) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_188_0, decode 300 e_188_1, decode 300 e_188_2, decode 300 e_188_3, decode 300 e_188_4, decode 300 e_188_5, decode 173 e_188_6] (fun x hx => ab_bits hx) qcov_188 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_188_0, qch_188_1, qch_188_2, qch_188_3, qch_188_4, qch_188_5, qch_188_6])

theorem qroot_189 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 189) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_189_0, decode 300 e_189_1, decode 300 e_189_2, decode 300 e_189_3, decode 300 e_189_4, decode 300 e_189_5, decode 173 e_189_6] (fun x hx => ab_bits hx) qcov_189 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_189_0, qch_189_1, qch_189_2, qch_189_3, qch_189_4, qch_189_5, qch_189_6])

theorem qroot_190 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 190) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_190_0, decode 300 e_190_1, decode 300 e_190_2, decode 300 e_190_3, decode 300 e_190_4, decode 300 e_190_5, decode 173 e_190_6] (fun x hx => ab_bits hx) qcov_190 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_190_0, qch_190_1, qch_190_2, qch_190_3, qch_190_4, qch_190_5, qch_190_6])

theorem qroot_191 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 191) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_191_0, decode 300 e_191_1, decode 300 e_191_2, decode 300 e_191_3, decode 300 e_191_4, decode 300 e_191_5, decode 173 e_191_6] (fun x hx => ab_bits hx) qcov_191 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_191_0, qch_191_1, qch_191_2, qch_191_3, qch_191_4, qch_191_5, qch_191_6])

theorem qroot_192 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 192) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_192_0, decode 300 e_192_1, decode 300 e_192_2, decode 300 e_192_3, decode 300 e_192_4, decode 300 e_192_5, decode 173 e_192_6] (fun x hx => ab_bits hx) qcov_192 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_192_0, qch_192_1, qch_192_2, qch_192_3, qch_192_4, qch_192_5, qch_192_6])

theorem qroot_193 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 193) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_193_0, decode 300 e_193_1, decode 300 e_193_2, decode 300 e_193_3, decode 300 e_193_4, decode 300 e_193_5, decode 173 e_193_6] (fun x hx => ab_bits hx) qcov_193 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_193_0, qch_193_1, qch_193_2, qch_193_3, qch_193_4, qch_193_5, qch_193_6])

theorem qroot_194 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 194) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_194_0, decode 300 e_194_1, decode 300 e_194_2, decode 300 e_194_3, decode 300 e_194_4, decode 300 e_194_5, decode 173 e_194_6] (fun x hx => ab_bits hx) qcov_194 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_194_0, qch_194_1, qch_194_2, qch_194_3, qch_194_4, qch_194_5, qch_194_6])

theorem qroot_195 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 195) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_195_0, decode 300 e_195_1, decode 300 e_195_2, decode 300 e_195_3, decode 300 e_195_4, decode 300 e_195_5, decode 173 e_195_6] (fun x hx => ab_bits hx) qcov_195 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_195_0, qch_195_1, qch_195_2, qch_195_3, qch_195_4, qch_195_5, qch_195_6])

theorem qroot_196 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 196) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_196_0, decode 300 e_196_1, decode 300 e_196_2, decode 300 e_196_3, decode 300 e_196_4, decode 300 e_196_5, decode 173 e_196_6] (fun x hx => ab_bits hx) qcov_196 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_196_0, qch_196_1, qch_196_2, qch_196_3, qch_196_4, qch_196_5, qch_196_6])

theorem qroot_197 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 197) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_197_0, decode 300 e_197_1, decode 300 e_197_2, decode 300 e_197_3, decode 300 e_197_4, decode 300 e_197_5, decode 173 e_197_6] (fun x hx => ab_bits hx) qcov_197 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_197_0, qch_197_1, qch_197_2, qch_197_3, qch_197_4, qch_197_5, qch_197_6])

theorem qroot_198 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 198) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_198_0, decode 300 e_198_1, decode 300 e_198_2, decode 300 e_198_3, decode 300 e_198_4, decode 300 e_198_5, decode 173 e_198_6] (fun x hx => ab_bits hx) qcov_198 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_198_0, qch_198_1, qch_198_2, qch_198_3, qch_198_4, qch_198_5, qch_198_6])

theorem qroot_199 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 199) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_199_0, decode 300 e_199_1, decode 300 e_199_2, decode 300 e_199_3, decode 300 e_199_4, decode 300 e_199_5, decode 173 e_199_6] (fun x hx => ab_bits hx) qcov_199 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_199_0, qch_199_1, qch_199_2, qch_199_3, qch_199_4, qch_199_5, qch_199_6])

theorem qroot_200 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 200) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_200_0, decode 300 e_200_1, decode 300 e_200_2, decode 300 e_200_3, decode 300 e_200_4, decode 300 e_200_5, decode 173 e_200_6] (fun x hx => ab_bits hx) qcov_200 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_200_0, qch_200_1, qch_200_2, qch_200_3, qch_200_4, qch_200_5, qch_200_6])

theorem qroot_201 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 201) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_201_0, decode 300 e_201_1, decode 300 e_201_2, decode 300 e_201_3, decode 300 e_201_4, decode 300 e_201_5, decode 173 e_201_6] (fun x hx => ab_bits hx) qcov_201 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_201_0, qch_201_1, qch_201_2, qch_201_3, qch_201_4, qch_201_5, qch_201_6])

theorem qroot_202 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 202) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_202_0, decode 300 e_202_1, decode 300 e_202_2, decode 300 e_202_3, decode 300 e_202_4, decode 300 e_202_5, decode 173 e_202_6] (fun x hx => ab_bits hx) qcov_202 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_202_0, qch_202_1, qch_202_2, qch_202_3, qch_202_4, qch_202_5, qch_202_6])

theorem qroot_203 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 203) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_203_0, decode 300 e_203_1, decode 300 e_203_2, decode 300 e_203_3, decode 300 e_203_4, decode 300 e_203_5, decode 173 e_203_6] (fun x hx => ab_bits hx) qcov_203 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_203_0, qch_203_1, qch_203_2, qch_203_3, qch_203_4, qch_203_5, qch_203_6])

theorem qroot_204 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 204) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_204_0, decode 300 e_204_1, decode 300 e_204_2, decode 300 e_204_3, decode 300 e_204_4, decode 300 e_204_5, decode 173 e_204_6] (fun x hx => ab_bits hx) qcov_204 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_204_0, qch_204_1, qch_204_2, qch_204_3, qch_204_4, qch_204_5, qch_204_6])

theorem qroot_205 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 205) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_205_0, decode 300 e_205_1, decode 300 e_205_2, decode 300 e_205_3, decode 300 e_205_4, decode 300 e_205_5, decode 173 e_205_6] (fun x hx => ab_bits hx) qcov_205 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_205_0, qch_205_1, qch_205_2, qch_205_3, qch_205_4, qch_205_5, qch_205_6])

theorem qroot_206 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 206) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_206_0, decode 300 e_206_1, decode 300 e_206_2, decode 300 e_206_3, decode 300 e_206_4, decode 300 e_206_5, decode 173 e_206_6] (fun x hx => ab_bits hx) qcov_206 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_206_0, qch_206_1, qch_206_2, qch_206_3, qch_206_4, qch_206_5, qch_206_6])

theorem qroot_207 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 207) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_207_0, decode 300 e_207_1, decode 300 e_207_2, decode 300 e_207_3, decode 300 e_207_4, decode 300 e_207_5, decode 173 e_207_6] (fun x hx => ab_bits hx) qcov_207 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_207_0, qch_207_1, qch_207_2, qch_207_3, qch_207_4, qch_207_5, qch_207_6])

theorem qroot_208 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 208) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_208_0, decode 300 e_208_1, decode 300 e_208_2, decode 300 e_208_3, decode 300 e_208_4, decode 300 e_208_5, decode 173 e_208_6] (fun x hx => ab_bits hx) qcov_208 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_208_0, qch_208_1, qch_208_2, qch_208_3, qch_208_4, qch_208_5, qch_208_6])

theorem qroot_209 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (AB 209) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_209_0, decode 300 e_209_1, decode 300 e_209_2, decode 300 e_209_3, decode 300 e_209_4, decode 300 e_209_5, decode 173 e_209_6] (fun x hx => ab_bits hx) qcov_209 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [qch_209_0, qch_209_1, qch_209_2, qch_209_3, qch_209_4, qch_209_5, qch_209_6])

end LRC.O7P2
