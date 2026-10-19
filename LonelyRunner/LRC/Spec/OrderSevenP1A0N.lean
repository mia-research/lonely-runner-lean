import LonelyRunner.LRC.Spec.OrderSevenP1BitsN
import LonelyRunner.LRC.Spec.OrderSevenP1C0N
import LonelyRunner.LRC.Spec.OrderSevenP1C1N
import LonelyRunner.LRC.Spec.OrderSevenP1C2N
import LonelyRunner.LRC.Spec.OrderSevenP1C3N
import LonelyRunner.LRC.Spec.OrderSevenP1C4N
import LonelyRunner.LRC.Spec.OrderSevenP1C5N
import LonelyRunner.LRC.Spec.OrderSevenP1C6N
import LonelyRunner.LRC.Spec.OrderSevenP1C7N
import LonelyRunner.LRC.Spec.OrderSevenP1C8N
import LonelyRunner.LRC.Spec.OrderSevenP1C9N

set_option maxRecDepth 100000

namespace LRC.O7U5

theorem proot_0 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 0) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_0_0, decode 300 e_0_1, decode 300 e_0_2, decode 300 e_0_3, decode 300 e_0_4, decode 103 e_0_5] (fun x hx => ub_bits hx) pcov_0 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_0_0, pch_0_1, pch_0_2, pch_0_3, pch_0_4, pch_0_5])

theorem proot_1 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 1) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_1_0, decode 300 e_1_1, decode 300 e_1_2, decode 300 e_1_3, decode 300 e_1_4, decode 92 e_1_5] (fun x hx => ub_bits hx) pcov_1 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_1_0, pch_1_1, pch_1_2, pch_1_3, pch_1_4, pch_1_5])

theorem proot_2 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 2) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_2_0, decode 300 e_2_1, decode 300 e_2_2, decode 300 e_2_3, decode 300 e_2_4, decode 102 e_2_5] (fun x hx => ub_bits hx) pcov_2 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_2_0, pch_2_1, pch_2_2, pch_2_3, pch_2_4, pch_2_5])

theorem proot_3 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 3) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_3_0, decode 300 e_3_1, decode 300 e_3_2, decode 300 e_3_3, decode 300 e_3_4, decode 102 e_3_5] (fun x hx => ub_bits hx) pcov_3 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_3_0, pch_3_1, pch_3_2, pch_3_3, pch_3_4, pch_3_5])

theorem proot_4 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 4) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_4_0, decode 300 e_4_1, decode 300 e_4_2, decode 300 e_4_3, decode 300 e_4_4, decode 92 e_4_5] (fun x hx => ub_bits hx) pcov_4 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_4_0, pch_4_1, pch_4_2, pch_4_3, pch_4_4, pch_4_5])

theorem proot_5 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 5) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_5_0, decode 300 e_5_1, decode 300 e_5_2, decode 300 e_5_3, decode 300 e_5_4, decode 104 e_5_5] (fun x hx => ub_bits hx) pcov_5 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_5_0, pch_5_1, pch_5_2, pch_5_3, pch_5_4, pch_5_5])

theorem proot_6 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 6) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_6_0, decode 300 e_6_1, decode 300 e_6_2, decode 300 e_6_3, decode 300 e_6_4, decode 94 e_6_5] (fun x hx => ub_bits hx) pcov_6 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_6_0, pch_6_1, pch_6_2, pch_6_3, pch_6_4, pch_6_5])

theorem proot_7 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 7) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_7_0, decode 300 e_7_1, decode 300 e_7_2, decode 300 e_7_3, decode 300 e_7_4, decode 85 e_7_5] (fun x hx => ub_bits hx) pcov_7 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_7_0, pch_7_1, pch_7_2, pch_7_3, pch_7_4, pch_7_5])

theorem proot_8 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 8) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_8_0, decode 300 e_8_1, decode 300 e_8_2, decode 300 e_8_3, decode 300 e_8_4, decode 93 e_8_5] (fun x hx => ub_bits hx) pcov_8 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_8_0, pch_8_1, pch_8_2, pch_8_3, pch_8_4, pch_8_5])

theorem proot_9 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 9) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_9_0, decode 300 e_9_1, decode 300 e_9_2, decode 300 e_9_3, decode 300 e_9_4, decode 87 e_9_5] (fun x hx => ub_bits hx) pcov_9 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_9_0, pch_9_1, pch_9_2, pch_9_3, pch_9_4, pch_9_5])

theorem proot_10 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 10) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_10_0, decode 300 e_10_1, decode 300 e_10_2, decode 300 e_10_3, decode 300 e_10_4, decode 80 e_10_5] (fun x hx => ub_bits hx) pcov_10 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_10_0, pch_10_1, pch_10_2, pch_10_3, pch_10_4, pch_10_5])

theorem proot_11 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 11) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_11_0, decode 300 e_11_1, decode 300 e_11_2, decode 300 e_11_3, decode 300 e_11_4, decode 96 e_11_5] (fun x hx => ub_bits hx) pcov_11 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_11_0, pch_11_1, pch_11_2, pch_11_3, pch_11_4, pch_11_5])

theorem proot_12 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 12) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_12_0, decode 300 e_12_1, decode 300 e_12_2, decode 300 e_12_3, decode 300 e_12_4, decode 96 e_12_5] (fun x hx => ub_bits hx) pcov_12 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_12_0, pch_12_1, pch_12_2, pch_12_3, pch_12_4, pch_12_5])

theorem proot_13 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 13) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_13_0, decode 300 e_13_1, decode 300 e_13_2, decode 300 e_13_3, decode 300 e_13_4, decode 85 e_13_5] (fun x hx => ub_bits hx) pcov_13 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_13_0, pch_13_1, pch_13_2, pch_13_3, pch_13_4, pch_13_5])

theorem proot_14 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 14) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_14_0, decode 300 e_14_1, decode 300 e_14_2, decode 300 e_14_3, decode 300 e_14_4, decode 93 e_14_5] (fun x hx => ub_bits hx) pcov_14 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_14_0, pch_14_1, pch_14_2, pch_14_3, pch_14_4, pch_14_5])

theorem proot_15 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 15) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_15_0, decode 300 e_15_1, decode 300 e_15_2, decode 300 e_15_3, decode 300 e_15_4, decode 86 e_15_5] (fun x hx => ub_bits hx) pcov_15 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_15_0, pch_15_1, pch_15_2, pch_15_3, pch_15_4, pch_15_5])

theorem proot_16 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 16) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_16_0, decode 300 e_16_1, decode 300 e_16_2, decode 300 e_16_3, decode 300 e_16_4, decode 80 e_16_5] (fun x hx => ub_bits hx) pcov_16 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_16_0, pch_16_1, pch_16_2, pch_16_3, pch_16_4, pch_16_5])

theorem proot_17 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 17) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_17_0, decode 300 e_17_1, decode 300 e_17_2, decode 300 e_17_3, decode 300 e_17_4, decode 98 e_17_5] (fun x hx => ub_bits hx) pcov_17 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_17_0, pch_17_1, pch_17_2, pch_17_3, pch_17_4, pch_17_5])

theorem proot_18 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 18) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_18_0, decode 300 e_18_1, decode 300 e_18_2, decode 300 e_18_3, decode 300 e_18_4, decode 95 e_18_5] (fun x hx => ub_bits hx) pcov_18 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_18_0, pch_18_1, pch_18_2, pch_18_3, pch_18_4, pch_18_5])

theorem proot_19 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 19) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_19_0, decode 300 e_19_1, decode 300 e_19_2, decode 300 e_19_3, decode 300 e_19_4, decode 83 e_19_5] (fun x hx => ub_bits hx) pcov_19 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_19_0, pch_19_1, pch_19_2, pch_19_3, pch_19_4, pch_19_5])

theorem proot_20 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 20) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_20_0, decode 300 e_20_1, decode 300 e_20_2, decode 300 e_20_3, decode 300 e_20_4, decode 91 e_20_5] (fun x hx => ub_bits hx) pcov_20 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_20_0, pch_20_1, pch_20_2, pch_20_3, pch_20_4, pch_20_5])

theorem proot_21 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 21) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_21_0, decode 300 e_21_1, decode 300 e_21_2, decode 300 e_21_3, decode 300 e_21_4, decode 84 e_21_5] (fun x hx => ub_bits hx) pcov_21 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_21_0, pch_21_1, pch_21_2, pch_21_3, pch_21_4, pch_21_5])

theorem proot_22 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 22) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_22_0, decode 300 e_22_1, decode 300 e_22_2, decode 300 e_22_3, decode 300 e_22_4, decode 79 e_22_5] (fun x hx => ub_bits hx) pcov_22 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_22_0, pch_22_1, pch_22_2, pch_22_3, pch_22_4, pch_22_5])

theorem proot_23 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 23) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_23_0, decode 300 e_23_1, decode 300 e_23_2, decode 300 e_23_3, decode 300 e_23_4, decode 96 e_23_5] (fun x hx => ub_bits hx) pcov_23 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_23_0, pch_23_1, pch_23_2, pch_23_3, pch_23_4, pch_23_5])

theorem proot_24 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 24) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_24_0, decode 300 e_24_1, decode 300 e_24_2, decode 300 e_24_3, decode 300 e_24_4, decode 98 e_24_5] (fun x hx => ub_bits hx) pcov_24 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_24_0, pch_24_1, pch_24_2, pch_24_3, pch_24_4, pch_24_5])

theorem proot_25 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 25) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_25_0, decode 300 e_25_1, decode 300 e_25_2, decode 300 e_25_3, decode 300 e_25_4, decode 96 e_25_5] (fun x hx => ub_bits hx) pcov_25 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_25_0, pch_25_1, pch_25_2, pch_25_3, pch_25_4, pch_25_5])

theorem proot_26 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 26) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_26_0, decode 300 e_26_1, decode 300 e_26_2, decode 300 e_26_3, decode 300 e_26_4, decode 84 e_26_5] (fun x hx => ub_bits hx) pcov_26 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_26_0, pch_26_1, pch_26_2, pch_26_3, pch_26_4, pch_26_5])

theorem proot_27 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 27) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_27_0, decode 300 e_27_1, decode 300 e_27_2, decode 300 e_27_3, decode 300 e_27_4, decode 86 e_27_5] (fun x hx => ub_bits hx) pcov_27 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_27_0, pch_27_1, pch_27_2, pch_27_3, pch_27_4, pch_27_5])

theorem proot_28 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 28) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_28_0, decode 300 e_28_1, decode 300 e_28_2, decode 300 e_28_3, decode 300 e_28_4, decode 82 e_28_5] (fun x hx => ub_bits hx) pcov_28 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_28_0, pch_28_1, pch_28_2, pch_28_3, pch_28_4, pch_28_5])

theorem proot_29 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 29) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_29_0, decode 300 e_29_1, decode 300 e_29_2, decode 300 e_29_3, decode 300 e_29_4, decode 93 e_29_5] (fun x hx => ub_bits hx) pcov_29 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_29_0, pch_29_1, pch_29_2, pch_29_3, pch_29_4, pch_29_5])

theorem proot_30 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 30) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_30_0, decode 300 e_30_1, decode 300 e_30_2, decode 300 e_30_3, decode 300 e_30_4, decode 93 e_30_5] (fun x hx => ub_bits hx) pcov_30 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_30_0, pch_30_1, pch_30_2, pch_30_3, pch_30_4, pch_30_5])

theorem proot_31 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 31) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_31_0, decode 300 e_31_1, decode 300 e_31_2, decode 300 e_31_3, decode 300 e_31_4, decode 96 e_31_5] (fun x hx => ub_bits hx) pcov_31 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_31_0, pch_31_1, pch_31_2, pch_31_3, pch_31_4, pch_31_5])

theorem proot_32 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 32) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_32_0, decode 300 e_32_1, decode 300 e_32_2, decode 300 e_32_3, decode 300 e_32_4, decode 82 e_32_5] (fun x hx => ub_bits hx) pcov_32 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_32_0, pch_32_1, pch_32_2, pch_32_3, pch_32_4, pch_32_5])

theorem proot_33 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 33) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_33_0, decode 300 e_33_1, decode 300 e_33_2, decode 300 e_33_3, decode 300 e_33_4, decode 86 e_33_5] (fun x hx => ub_bits hx) pcov_33 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_33_0, pch_33_1, pch_33_2, pch_33_3, pch_33_4, pch_33_5])

theorem proot_34 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 34) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_34_0, decode 300 e_34_1, decode 300 e_34_2, decode 300 e_34_3, decode 300 e_34_4, decode 82 e_34_5] (fun x hx => ub_bits hx) pcov_34 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_34_0, pch_34_1, pch_34_2, pch_34_3, pch_34_4, pch_34_5])

theorem proot_35 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 35) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_35_0, decode 300 e_35_1, decode 300 e_35_2, decode 300 e_35_3, decode 300 e_35_4, decode 93 e_35_5] (fun x hx => ub_bits hx) pcov_35 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_35_0, pch_35_1, pch_35_2, pch_35_3, pch_35_4, pch_35_5])

theorem proot_36 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 36) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_36_0, decode 300 e_36_1, decode 300 e_36_2, decode 300 e_36_3, decode 300 e_36_4, decode 96 e_36_5] (fun x hx => ub_bits hx) pcov_36 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_36_0, pch_36_1, pch_36_2, pch_36_3, pch_36_4, pch_36_5])

theorem proot_37 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 37) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_37_0, decode 300 e_37_1, decode 300 e_37_2, decode 300 e_37_3, decode 300 e_37_4, decode 97 e_37_5] (fun x hx => ub_bits hx) pcov_37 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_37_0, pch_37_1, pch_37_2, pch_37_3, pch_37_4, pch_37_5])

theorem proot_38 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 38) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_38_0, decode 300 e_38_1, decode 300 e_38_2, decode 300 e_38_3, decode 300 e_38_4, decode 81 e_38_5] (fun x hx => ub_bits hx) pcov_38 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_38_0, pch_38_1, pch_38_2, pch_38_3, pch_38_4, pch_38_5])

theorem proot_39 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 39) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_39_0, decode 300 e_39_1, decode 300 e_39_2, decode 300 e_39_3, decode 300 e_39_4, decode 86 e_39_5] (fun x hx => ub_bits hx) pcov_39 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_39_0, pch_39_1, pch_39_2, pch_39_3, pch_39_4, pch_39_5])

theorem proot_40 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 40) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_40_0, decode 300 e_40_1, decode 300 e_40_2, decode 300 e_40_3, decode 300 e_40_4, decode 96 e_40_5] (fun x hx => ub_bits hx) pcov_40 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_40_0, pch_40_1, pch_40_2, pch_40_3, pch_40_4, pch_40_5])

theorem proot_41 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 41) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_41_0, decode 300 e_41_1, decode 300 e_41_2, decode 300 e_41_3, decode 300 e_41_4, decode 95 e_41_5] (fun x hx => ub_bits hx) pcov_41 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_41_0, pch_41_1, pch_41_2, pch_41_3, pch_41_4, pch_41_5])

theorem proot_42 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 42) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_42_0, decode 300 e_42_1, decode 300 e_42_2, decode 300 e_42_3, decode 300 e_42_4, decode 95 e_42_5] (fun x hx => ub_bits hx) pcov_42 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_42_0, pch_42_1, pch_42_2, pch_42_3, pch_42_4, pch_42_5])

theorem proot_43 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 43) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_43_0, decode 300 e_43_1, decode 300 e_43_2, decode 300 e_43_3, decode 300 e_43_4, decode 97 e_43_5] (fun x hx => ub_bits hx) pcov_43 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_43_0, pch_43_1, pch_43_2, pch_43_3, pch_43_4, pch_43_5])

theorem proot_44 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 44) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_44_0, decode 300 e_44_1, decode 300 e_44_2, decode 300 e_44_3, decode 300 e_44_4, decode 81 e_44_5] (fun x hx => ub_bits hx) pcov_44 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_44_0, pch_44_1, pch_44_2, pch_44_3, pch_44_4, pch_44_5])

theorem proot_45 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 45) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_45_0, decode 300 e_45_1, decode 300 e_45_2, decode 300 e_45_3, decode 300 e_45_4, decode 84 e_45_5] (fun x hx => ub_bits hx) pcov_45 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_45_0, pch_45_1, pch_45_2, pch_45_3, pch_45_4, pch_45_5])

theorem proot_46 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 46) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_46_0, decode 300 e_46_1, decode 300 e_46_2, decode 300 e_46_3, decode 300 e_46_4, decode 96 e_46_5] (fun x hx => ub_bits hx) pcov_46 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_46_0, pch_46_1, pch_46_2, pch_46_3, pch_46_4, pch_46_5])

theorem proot_47 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 47) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_47_0, decode 300 e_47_1, decode 300 e_47_2, decode 300 e_47_3, decode 300 e_47_4, decode 92 e_47_5] (fun x hx => ub_bits hx) pcov_47 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_47_0, pch_47_1, pch_47_2, pch_47_3, pch_47_4, pch_47_5])

theorem proot_48 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 48) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_48_0, decode 300 e_48_1, decode 300 e_48_2, decode 300 e_48_3, decode 300 e_48_4, decode 89 e_48_5] (fun x hx => ub_bits hx) pcov_48 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_48_0, pch_48_1, pch_48_2, pch_48_3, pch_48_4, pch_48_5])

theorem proot_49 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 49) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_49_0, decode 300 e_49_1, decode 300 e_49_2, decode 300 e_49_3, decode 300 e_49_4, decode 99 e_49_5] (fun x hx => ub_bits hx) pcov_49 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_49_0, pch_49_1, pch_49_2, pch_49_3, pch_49_4, pch_49_5])

theorem proot_50 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 50) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_50_0, decode 300 e_50_1, decode 300 e_50_2, decode 300 e_50_3, decode 300 e_50_4, decode 82 e_50_5] (fun x hx => ub_bits hx) pcov_50 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_50_0, pch_50_1, pch_50_2, pch_50_3, pch_50_4, pch_50_5])

theorem proot_51 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 51) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_51_0, decode 300 e_51_1, decode 300 e_51_2, decode 300 e_51_3, decode 300 e_51_4, decode 83 e_51_5] (fun x hx => ub_bits hx) pcov_51 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_51_0, pch_51_1, pch_51_2, pch_51_3, pch_51_4, pch_51_5])

theorem proot_52 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 52) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_52_0, decode 300 e_52_1, decode 300 e_52_2, decode 300 e_52_3, decode 300 e_52_4, decode 89 e_52_5] (fun x hx => ub_bits hx) pcov_52 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_52_0, pch_52_1, pch_52_2, pch_52_3, pch_52_4, pch_52_5])

theorem proot_53 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 53) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_53_0, decode 300 e_53_1, decode 300 e_53_2, decode 300 e_53_3, decode 300 e_53_4, decode 79 e_53_5] (fun x hx => ub_bits hx) pcov_53 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_53_0, pch_53_1, pch_53_2, pch_53_3, pch_53_4, pch_53_5])

theorem proot_54 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 54) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_54_0, decode 300 e_54_1, decode 300 e_54_2, decode 300 e_54_3, decode 300 e_54_4, decode 88 e_54_5] (fun x hx => ub_bits hx) pcov_54 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_54_0, pch_54_1, pch_54_2, pch_54_3, pch_54_4, pch_54_5])

theorem proot_55 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 55) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_55_0, decode 300 e_55_1, decode 300 e_55_2, decode 300 e_55_3, decode 300 e_55_4, decode 88 e_55_5] (fun x hx => ub_bits hx) pcov_55 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_55_0, pch_55_1, pch_55_2, pch_55_3, pch_55_4, pch_55_5])

theorem proot_56 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 56) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_56_0, decode 300 e_56_1, decode 300 e_56_2, decode 300 e_56_3, decode 300 e_56_4, decode 80 e_56_5] (fun x hx => ub_bits hx) pcov_56 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_56_0, pch_56_1, pch_56_2, pch_56_3, pch_56_4, pch_56_5])

theorem proot_57 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 57) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_57_0, decode 300 e_57_1, decode 300 e_57_2, decode 300 e_57_3, decode 300 e_57_4, decode 82 e_57_5] (fun x hx => ub_bits hx) pcov_57 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_57_0, pch_57_1, pch_57_2, pch_57_3, pch_57_4, pch_57_5])

theorem proot_58 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 58) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_58_0, decode 300 e_58_1, decode 300 e_58_2, decode 300 e_58_3, decode 300 e_58_4, decode 92 e_58_5] (fun x hx => ub_bits hx) pcov_58 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_58_0, pch_58_1, pch_58_2, pch_58_3, pch_58_4, pch_58_5])

theorem proot_59 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 59) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_59_0, decode 300 e_59_1, decode 300 e_59_2, decode 300 e_59_3, decode 300 e_59_4, decode 79 e_59_5] (fun x hx => ub_bits hx) pcov_59 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_59_0, pch_59_1, pch_59_2, pch_59_3, pch_59_4, pch_59_5])

theorem proot_60 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 60) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_60_0, decode 300 e_60_1, decode 300 e_60_2, decode 300 e_60_3, decode 300 e_60_4, decode 88 e_60_5] (fun x hx => ub_bits hx) pcov_60 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_60_0, pch_60_1, pch_60_2, pch_60_3, pch_60_4, pch_60_5])

theorem proot_61 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 61) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_61_0, decode 300 e_61_1, decode 300 e_61_2, decode 300 e_61_3, decode 300 e_61_4, decode 89 e_61_5] (fun x hx => ub_bits hx) pcov_61 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_61_0, pch_61_1, pch_61_2, pch_61_3, pch_61_4, pch_61_5])

theorem proot_62 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 62) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_62_0, decode 300 e_62_1, decode 300 e_62_2, decode 300 e_62_3, decode 300 e_62_4, decode 82 e_62_5] (fun x hx => ub_bits hx) pcov_62 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_62_0, pch_62_1, pch_62_2, pch_62_3, pch_62_4, pch_62_5])

theorem proot_63 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 63) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_63_0, decode 300 e_63_1, decode 300 e_63_2, decode 300 e_63_3, decode 300 e_63_4, decode 81 e_63_5] (fun x hx => ub_bits hx) pcov_63 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_63_0, pch_63_1, pch_63_2, pch_63_3, pch_63_4, pch_63_5])

theorem proot_64 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 64) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_64_0, decode 300 e_64_1, decode 300 e_64_2, decode 300 e_64_3, decode 300 e_64_4, decode 85 e_64_5] (fun x hx => ub_bits hx) pcov_64 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_64_0, pch_64_1, pch_64_2, pch_64_3, pch_64_4, pch_64_5])

theorem proot_65 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 65) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_65_0, decode 300 e_65_1, decode 300 e_65_2, decode 300 e_65_3, decode 300 e_65_4, decode 84 e_65_5] (fun x hx => ub_bits hx) pcov_65 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_65_0, pch_65_1, pch_65_2, pch_65_3, pch_65_4, pch_65_5])

theorem proot_66 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 66) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_66_0, decode 300 e_66_1, decode 300 e_66_2, decode 300 e_66_3, decode 300 e_66_4, decode 93 e_66_5] (fun x hx => ub_bits hx) pcov_66 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_66_0, pch_66_1, pch_66_2, pch_66_3, pch_66_4, pch_66_5])

theorem proot_67 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 67) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_67_0, decode 300 e_67_1, decode 300 e_67_2, decode 300 e_67_3, decode 300 e_67_4, decode 95 e_67_5] (fun x hx => ub_bits hx) pcov_67 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_67_0, pch_67_1, pch_67_2, pch_67_3, pch_67_4, pch_67_5])

theorem proot_68 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 68) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_68_0, decode 300 e_68_1, decode 300 e_68_2, decode 300 e_68_3, decode 300 e_68_4, decode 87 e_68_5] (fun x hx => ub_bits hx) pcov_68 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_68_0, pch_68_1, pch_68_2, pch_68_3, pch_68_4, pch_68_5])

theorem proot_69 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 69) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_69_0, decode 300 e_69_1, decode 300 e_69_2, decode 300 e_69_3, decode 300 e_69_4, decode 85 e_69_5] (fun x hx => ub_bits hx) pcov_69 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_69_0, pch_69_1, pch_69_2, pch_69_3, pch_69_4, pch_69_5])

theorem proot_70 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 70) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_70_0, decode 300 e_70_1, decode 300 e_70_2, decode 300 e_70_3, decode 300 e_70_4, decode 90 e_70_5] (fun x hx => ub_bits hx) pcov_70 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_70_0, pch_70_1, pch_70_2, pch_70_3, pch_70_4, pch_70_5])

theorem proot_71 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 71) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_71_0, decode 300 e_71_1, decode 300 e_71_2, decode 300 e_71_3, decode 300 e_71_4, decode 86 e_71_5] (fun x hx => ub_bits hx) pcov_71 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_71_0, pch_71_1, pch_71_2, pch_71_3, pch_71_4, pch_71_5])

theorem proot_72 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 72) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_72_0, decode 300 e_72_1, decode 300 e_72_2, decode 300 e_72_3, decode 300 e_72_4, decode 81 e_72_5] (fun x hx => ub_bits hx) pcov_72 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_72_0, pch_72_1, pch_72_2, pch_72_3, pch_72_4, pch_72_5])

theorem proot_73 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 73) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_73_0, decode 300 e_73_1, decode 300 e_73_2, decode 300 e_73_3, decode 300 e_73_4, decode 80 e_73_5] (fun x hx => ub_bits hx) pcov_73 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_73_0, pch_73_1, pch_73_2, pch_73_3, pch_73_4, pch_73_5])

theorem proot_74 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 74) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_74_0, decode 300 e_74_1, decode 300 e_74_2, decode 300 e_74_3, decode 300 e_74_4, decode 90 e_74_5] (fun x hx => ub_bits hx) pcov_74 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_74_0, pch_74_1, pch_74_2, pch_74_3, pch_74_4, pch_74_5])

theorem proot_75 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 75) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_75_0, decode 300 e_75_1, decode 300 e_75_2, decode 300 e_75_3, decode 300 e_75_4, decode 93 e_75_5] (fun x hx => ub_bits hx) pcov_75 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_75_0, pch_75_1, pch_75_2, pch_75_3, pch_75_4, pch_75_5])

theorem proot_76 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 76) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_76_0, decode 300 e_76_1, decode 300 e_76_2, decode 300 e_76_3, decode 300 e_76_4, decode 76 e_76_5] (fun x hx => ub_bits hx) pcov_76 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_76_0, pch_76_1, pch_76_2, pch_76_3, pch_76_4, pch_76_5])

theorem proot_77 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 77) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_77_0, decode 300 e_77_1, decode 300 e_77_2, decode 300 e_77_3, decode 300 e_77_4, decode 82 e_77_5] (fun x hx => ub_bits hx) pcov_77 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_77_0, pch_77_1, pch_77_2, pch_77_3, pch_77_4, pch_77_5])

theorem proot_78 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 78) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_78_0, decode 300 e_78_1, decode 300 e_78_2, decode 300 e_78_3, decode 300 e_78_4, decode 81 e_78_5] (fun x hx => ub_bits hx) pcov_78 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_78_0, pch_78_1, pch_78_2, pch_78_3, pch_78_4, pch_78_5])

theorem proot_79 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 79) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_79_0, decode 300 e_79_1, decode 300 e_79_2, decode 300 e_79_3, decode 300 e_79_4, decode 75 e_79_5] (fun x hx => ub_bits hx) pcov_79 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_79_0, pch_79_1, pch_79_2, pch_79_3, pch_79_4, pch_79_5])

theorem proot_80 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 80) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_80_0, decode 300 e_80_1, decode 300 e_80_2, decode 300 e_80_3, decode 300 e_80_4, decode 88 e_80_5] (fun x hx => ub_bits hx) pcov_80 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_80_0, pch_80_1, pch_80_2, pch_80_3, pch_80_4, pch_80_5])

theorem proot_81 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 81) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_81_0, decode 300 e_81_1, decode 300 e_81_2, decode 300 e_81_3, decode 300 e_81_4, decode 92 e_81_5] (fun x hx => ub_bits hx) pcov_81 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_81_0, pch_81_1, pch_81_2, pch_81_3, pch_81_4, pch_81_5])

theorem proot_82 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 82) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_82_0, decode 300 e_82_1, decode 300 e_82_2, decode 300 e_82_3, decode 300 e_82_4, decode 71 e_82_5] (fun x hx => ub_bits hx) pcov_82 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_82_0, pch_82_1, pch_82_2, pch_82_3, pch_82_4, pch_82_5])

theorem proot_83 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 83) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_83_0, decode 300 e_83_1, decode 300 e_83_2, decode 300 e_83_3, decode 300 e_83_4, decode 75 e_83_5] (fun x hx => ub_bits hx) pcov_83 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_83_0, pch_83_1, pch_83_2, pch_83_3, pch_83_4, pch_83_5])

theorem proot_84 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 84) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_84_0, decode 300 e_84_1, decode 300 e_84_2, decode 300 e_84_3, decode 300 e_84_4, decode 81 e_84_5] (fun x hx => ub_bits hx) pcov_84 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_84_0, pch_84_1, pch_84_2, pch_84_3, pch_84_4, pch_84_5])

theorem proot_85 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 85) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_85_0, decode 300 e_85_1, decode 300 e_85_2, decode 300 e_85_3, decode 300 e_85_4, decode 75 e_85_5] (fun x hx => ub_bits hx) pcov_85 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_85_0, pch_85_1, pch_85_2, pch_85_3, pch_85_4, pch_85_5])

theorem proot_86 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 86) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_86_0, decode 300 e_86_1, decode 300 e_86_2, decode 300 e_86_3, decode 300 e_86_4, decode 86 e_86_5] (fun x hx => ub_bits hx) pcov_86 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_86_0, pch_86_1, pch_86_2, pch_86_3, pch_86_4, pch_86_5])

theorem proot_87 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 87) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_87_0, decode 300 e_87_1, decode 300 e_87_2, decode 300 e_87_3, decode 300 e_87_4, decode 92 e_87_5] (fun x hx => ub_bits hx) pcov_87 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_87_0, pch_87_1, pch_87_2, pch_87_3, pch_87_4, pch_87_5])

theorem proot_88 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 88) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_88_0, decode 300 e_88_1, decode 300 e_88_2, decode 300 e_88_3, decode 300 e_88_4, decode 71 e_88_5] (fun x hx => ub_bits hx) pcov_88 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_88_0, pch_88_1, pch_88_2, pch_88_3, pch_88_4, pch_88_5])

theorem proot_89 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 89) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_89_0, decode 300 e_89_1, decode 300 e_89_2, decode 300 e_89_3, decode 300 e_89_4, decode 75 e_89_5] (fun x hx => ub_bits hx) pcov_89 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_89_0, pch_89_1, pch_89_2, pch_89_3, pch_89_4, pch_89_5])

theorem proot_90 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 90) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_90_0, decode 300 e_90_1, decode 300 e_90_2, decode 300 e_90_3, decode 300 e_90_4, decode 90 e_90_5] (fun x hx => ub_bits hx) pcov_90 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_90_0, pch_90_1, pch_90_2, pch_90_3, pch_90_4, pch_90_5])

theorem proot_91 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 91) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_91_0, decode 300 e_91_1, decode 300 e_91_2, decode 300 e_91_3, decode 300 e_91_4, decode 75 e_91_5] (fun x hx => ub_bits hx) pcov_91 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_91_0, pch_91_1, pch_91_2, pch_91_3, pch_91_4, pch_91_5])

theorem proot_92 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 92) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_92_0, decode 300 e_92_1, decode 300 e_92_2, decode 300 e_92_3, decode 300 e_92_4, decode 86 e_92_5] (fun x hx => ub_bits hx) pcov_92 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_92_0, pch_92_1, pch_92_2, pch_92_3, pch_92_4, pch_92_5])

theorem proot_93 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 93) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_93_0, decode 300 e_93_1, decode 300 e_93_2, decode 300 e_93_3, decode 300 e_93_4, decode 89 e_93_5] (fun x hx => ub_bits hx) pcov_93 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_93_0, pch_93_1, pch_93_2, pch_93_3, pch_93_4, pch_93_5])

theorem proot_94 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 94) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_94_0, decode 300 e_94_1, decode 300 e_94_2, decode 300 e_94_3, decode 300 e_94_4, decode 73 e_94_5] (fun x hx => ub_bits hx) pcov_94 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_94_0, pch_94_1, pch_94_2, pch_94_3, pch_94_4, pch_94_5])

theorem proot_95 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 95) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_95_0, decode 300 e_95_1, decode 300 e_95_2, decode 300 e_95_3, decode 300 e_95_4, decode 75 e_95_5] (fun x hx => ub_bits hx) pcov_95 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_95_0, pch_95_1, pch_95_2, pch_95_3, pch_95_4, pch_95_5])

theorem proot_96 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 96) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_96_0, decode 300 e_96_1, decode 300 e_96_2, decode 300 e_96_3, decode 300 e_96_4, decode 88 e_96_5] (fun x hx => ub_bits hx) pcov_96 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_96_0, pch_96_1, pch_96_2, pch_96_3, pch_96_4, pch_96_5])

theorem proot_97 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 97) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_97_0, decode 300 e_97_1, decode 300 e_97_2, decode 300 e_97_3, decode 300 e_97_4, decode 84 e_97_5] (fun x hx => ub_bits hx) pcov_97 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_97_0, pch_97_1, pch_97_2, pch_97_3, pch_97_4, pch_97_5])

theorem proot_98 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 98) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_98_0, decode 300 e_98_1, decode 300 e_98_2, decode 300 e_98_3, decode 300 e_98_4, decode 75 e_98_5] (fun x hx => ub_bits hx) pcov_98 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_98_0, pch_98_1, pch_98_2, pch_98_3, pch_98_4, pch_98_5])

theorem proot_99 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 99) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_99_0, decode 300 e_99_1, decode 300 e_99_2, decode 300 e_99_3, decode 300 e_99_4, decode 77 e_99_5] (fun x hx => ub_bits hx) pcov_99 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_99_0, pch_99_1, pch_99_2, pch_99_3, pch_99_4, pch_99_5])

theorem proot_100 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 100) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_100_0, decode 300 e_100_1, decode 300 e_100_2, decode 300 e_100_3, decode 300 e_100_4, decode 83 e_100_5] (fun x hx => ub_bits hx) pcov_100 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_100_0, pch_100_1, pch_100_2, pch_100_3, pch_100_4, pch_100_5])

theorem proot_101 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 101) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_101_0, decode 300 e_101_1, decode 300 e_101_2, decode 300 e_101_3, decode 300 e_101_4, decode 75 e_101_5] (fun x hx => ub_bits hx) pcov_101 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_101_0, pch_101_1, pch_101_2, pch_101_3, pch_101_4, pch_101_5])

theorem proot_102 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 102) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_102_0, decode 300 e_102_1, decode 300 e_102_2, decode 300 e_102_3, decode 300 e_102_4, decode 89 e_102_5] (fun x hx => ub_bits hx) pcov_102 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_102_0, pch_102_1, pch_102_2, pch_102_3, pch_102_4, pch_102_5])

theorem proot_103 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 103) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_103_0, decode 300 e_103_1, decode 300 e_103_2, decode 300 e_103_3, decode 300 e_103_4, decode 88 e_103_5] (fun x hx => ub_bits hx) pcov_103 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_103_0, pch_103_1, pch_103_2, pch_103_3, pch_103_4, pch_103_5])

theorem proot_104 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 104) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_104_0, decode 300 e_104_1, decode 300 e_104_2, decode 300 e_104_3, decode 300 e_104_4, decode 75 e_104_5] (fun x hx => ub_bits hx) pcov_104 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_104_0, pch_104_1, pch_104_2, pch_104_3, pch_104_4, pch_104_5])

theorem proot_105 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 105) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_105_0, decode 300 e_105_1, decode 300 e_105_2, decode 300 e_105_3, decode 300 e_105_4, decode 77 e_105_5] (fun x hx => ub_bits hx) pcov_105 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_105_0, pch_105_1, pch_105_2, pch_105_3, pch_105_4, pch_105_5])

theorem proot_106 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 106) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_106_0, decode 300 e_106_1, decode 300 e_106_2, decode 300 e_106_3, decode 300 e_106_4, decode 83 e_106_5] (fun x hx => ub_bits hx) pcov_106 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_106_0, pch_106_1, pch_106_2, pch_106_3, pch_106_4, pch_106_5])

theorem proot_107 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 107) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_107_0, decode 300 e_107_1, decode 300 e_107_2, decode 300 e_107_3, decode 300 e_107_4, decode 72 e_107_5] (fun x hx => ub_bits hx) pcov_107 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_107_0, pch_107_1, pch_107_2, pch_107_3, pch_107_4, pch_107_5])

theorem proot_108 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 108) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_108_0, decode 300 e_108_1, decode 300 e_108_2, decode 300 e_108_3, decode 300 e_108_4, decode 87 e_108_5] (fun x hx => ub_bits hx) pcov_108 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_108_0, pch_108_1, pch_108_2, pch_108_3, pch_108_4, pch_108_5])

theorem proot_109 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 109) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_109_0, decode 300 e_109_1, decode 300 e_109_2, decode 300 e_109_3, decode 300 e_109_4, decode 85 e_109_5] (fun x hx => ub_bits hx) pcov_109 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_109_0, pch_109_1, pch_109_2, pch_109_3, pch_109_4, pch_109_5])

theorem proot_110 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 110) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_110_0, decode 300 e_110_1, decode 300 e_110_2, decode 300 e_110_3, decode 300 e_110_4, decode 80 e_110_5] (fun x hx => ub_bits hx) pcov_110 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_110_0, pch_110_1, pch_110_2, pch_110_3, pch_110_4, pch_110_5])

theorem proot_111 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 111) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_111_0, decode 300 e_111_1, decode 300 e_111_2, decode 300 e_111_3, decode 300 e_111_4, decode 77 e_111_5] (fun x hx => ub_bits hx) pcov_111 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_111_0, pch_111_1, pch_111_2, pch_111_3, pch_111_4, pch_111_5])

theorem proot_112 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 112) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_112_0, decode 300 e_112_1, decode 300 e_112_2, decode 300 e_112_3, decode 300 e_112_4, decode 87 e_112_5] (fun x hx => ub_bits hx) pcov_112 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_112_0, pch_112_1, pch_112_2, pch_112_3, pch_112_4, pch_112_5])

theorem proot_113 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 113) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_113_0, decode 300 e_113_1, decode 300 e_113_2, decode 300 e_113_3, decode 300 e_113_4, decode 73 e_113_5] (fun x hx => ub_bits hx) pcov_113 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_113_0, pch_113_1, pch_113_2, pch_113_3, pch_113_4, pch_113_5])

theorem proot_114 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 114) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_114_0, decode 300 e_114_1, decode 300 e_114_2, decode 300 e_114_3, decode 300 e_114_4, decode 87 e_114_5] (fun x hx => ub_bits hx) pcov_114 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_114_0, pch_114_1, pch_114_2, pch_114_3, pch_114_4, pch_114_5])

theorem proot_115 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 115) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_115_0, decode 300 e_115_1, decode 300 e_115_2, decode 300 e_115_3, decode 300 e_115_4, decode 84 e_115_5] (fun x hx => ub_bits hx) pcov_115 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_115_0, pch_115_1, pch_115_2, pch_115_3, pch_115_4, pch_115_5])

theorem proot_116 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 116) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_116_0, decode 300 e_116_1, decode 300 e_116_2, decode 300 e_116_3, decode 300 e_116_4, decode 81 e_116_5] (fun x hx => ub_bits hx) pcov_116 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_116_0, pch_116_1, pch_116_2, pch_116_3, pch_116_4, pch_116_5])

theorem proot_117 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 117) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_117_0, decode 300 e_117_1, decode 300 e_117_2, decode 300 e_117_3, decode 300 e_117_4, decode 79 e_117_5] (fun x hx => ub_bits hx) pcov_117 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_117_0, pch_117_1, pch_117_2, pch_117_3, pch_117_4, pch_117_5])

theorem proot_118 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 118) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_118_0, decode 300 e_118_1, decode 300 e_118_2, decode 300 e_118_3, decode 300 e_118_4, decode 88 e_118_5] (fun x hx => ub_bits hx) pcov_118 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_118_0, pch_118_1, pch_118_2, pch_118_3, pch_118_4, pch_118_5])

theorem proot_119 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 119) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_119_0, decode 300 e_119_1, decode 300 e_119_2, decode 300 e_119_3, decode 300 e_119_4, decode 73 e_119_5] (fun x hx => ub_bits hx) pcov_119 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_119_0, pch_119_1, pch_119_2, pch_119_3, pch_119_4, pch_119_5])

theorem proot_120 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 120) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_120_0, decode 300 e_120_1, decode 300 e_120_2, decode 300 e_120_3, decode 300 e_120_4, decode 97 e_120_5] (fun x hx => ub_bits hx) pcov_120 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_120_0, pch_120_1, pch_120_2, pch_120_3, pch_120_4, pch_120_5])

theorem proot_121 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 121) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_121_0, decode 300 e_121_1, decode 300 e_121_2, decode 300 e_121_3, decode 300 e_121_4, decode 88 e_121_5] (fun x hx => ub_bits hx) pcov_121 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_121_0, pch_121_1, pch_121_2, pch_121_3, pch_121_4, pch_121_5])

theorem proot_122 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 122) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_122_0, decode 300 e_122_1, decode 300 e_122_2, decode 300 e_122_3, decode 300 e_122_4, decode 78 e_122_5] (fun x hx => ub_bits hx) pcov_122 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_122_0, pch_122_1, pch_122_2, pch_122_3, pch_122_4, pch_122_5])

theorem proot_123 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 123) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_123_0, decode 300 e_123_1, decode 300 e_123_2, decode 300 e_123_3, decode 300 e_123_4, decode 77 e_123_5] (fun x hx => ub_bits hx) pcov_123 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_123_0, pch_123_1, pch_123_2, pch_123_3, pch_123_4, pch_123_5])

theorem proot_124 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 124) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_124_0, decode 300 e_124_1, decode 300 e_124_2, decode 300 e_124_3, decode 300 e_124_4, decode 89 e_124_5] (fun x hx => ub_bits hx) pcov_124 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_124_0, pch_124_1, pch_124_2, pch_124_3, pch_124_4, pch_124_5])

theorem proot_125 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 125) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_125_0, decode 300 e_125_1, decode 300 e_125_2, decode 300 e_125_3, decode 300 e_125_4, decode 99 e_125_5] (fun x hx => ub_bits hx) pcov_125 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_125_0, pch_125_1, pch_125_2, pch_125_3, pch_125_4, pch_125_5])

theorem proot_126 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 126) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_126_0, decode 300 e_126_1, decode 300 e_126_2, decode 300 e_126_3, decode 300 e_126_4, decode 89 e_126_5] (fun x hx => ub_bits hx) pcov_126 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_126_0, pch_126_1, pch_126_2, pch_126_3, pch_126_4, pch_126_5])

theorem proot_127 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 127) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_127_0, decode 300 e_127_1, decode 300 e_127_2, decode 300 e_127_3, decode 300 e_127_4, decode 89 e_127_5] (fun x hx => ub_bits hx) pcov_127 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_127_0, pch_127_1, pch_127_2, pch_127_3, pch_127_4, pch_127_5])

theorem proot_128 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 128) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_128_0, decode 300 e_128_1, decode 300 e_128_2, decode 300 e_128_3, decode 300 e_128_4, decode 77 e_128_5] (fun x hx => ub_bits hx) pcov_128 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_128_0, pch_128_1, pch_128_2, pch_128_3, pch_128_4, pch_128_5])

theorem proot_129 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 129) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_129_0, decode 300 e_129_1, decode 300 e_129_2, decode 300 e_129_3, decode 300 e_129_4, decode 77 e_129_5] (fun x hx => ub_bits hx) pcov_129 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_129_0, pch_129_1, pch_129_2, pch_129_3, pch_129_4, pch_129_5])

theorem proot_130 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 130) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_130_0, decode 300 e_130_1, decode 300 e_130_2, decode 300 e_130_3, decode 300 e_130_4, decode 90 e_130_5] (fun x hx => ub_bits hx) pcov_130 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_130_0, pch_130_1, pch_130_2, pch_130_3, pch_130_4, pch_130_5])

theorem proot_131 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 131) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_131_0, decode 300 e_131_1, decode 300 e_131_2, decode 300 e_131_3, decode 300 e_131_4, decode 91 e_131_5] (fun x hx => ub_bits hx) pcov_131 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_131_0, pch_131_1, pch_131_2, pch_131_3, pch_131_4, pch_131_5])

theorem proot_132 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 132) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_132_0, decode 300 e_132_1, decode 300 e_132_2, decode 300 e_132_3, decode 300 e_132_4, decode 79 e_132_5] (fun x hx => ub_bits hx) pcov_132 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_132_0, pch_132_1, pch_132_2, pch_132_3, pch_132_4, pch_132_5])

theorem proot_133 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 133) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_133_0, decode 300 e_133_1, decode 300 e_133_2, decode 300 e_133_3, decode 300 e_133_4, decode 89 e_133_5] (fun x hx => ub_bits hx) pcov_133 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_133_0, pch_133_1, pch_133_2, pch_133_3, pch_133_4, pch_133_5])

theorem proot_134 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 134) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_134_0, decode 300 e_134_1, decode 300 e_134_2, decode 300 e_134_3, decode 300 e_134_4, decode 77 e_134_5] (fun x hx => ub_bits hx) pcov_134 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_134_0, pch_134_1, pch_134_2, pch_134_3, pch_134_4, pch_134_5])

theorem proot_135 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 135) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_135_0, decode 300 e_135_1, decode 300 e_135_2, decode 300 e_135_3, decode 300 e_135_4, decode 77 e_135_5] (fun x hx => ub_bits hx) pcov_135 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_135_0, pch_135_1, pch_135_2, pch_135_3, pch_135_4, pch_135_5])

theorem proot_136 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 136) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_136_0, decode 300 e_136_1, decode 300 e_136_2, decode 300 e_136_3, decode 300 e_136_4, decode 94 e_136_5] (fun x hx => ub_bits hx) pcov_136 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_136_0, pch_136_1, pch_136_2, pch_136_3, pch_136_4, pch_136_5])

theorem proot_137 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 137) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_137_0, decode 300 e_137_1, decode 300 e_137_2, decode 300 e_137_3, decode 300 e_137_4, decode 86 e_137_5] (fun x hx => ub_bits hx) pcov_137 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_137_0, pch_137_1, pch_137_2, pch_137_3, pch_137_4, pch_137_5])

theorem proot_138 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 138) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_138_0, decode 300 e_138_1, decode 300 e_138_2, decode 300 e_138_3, decode 300 e_138_4, decode 87 e_138_5] (fun x hx => ub_bits hx) pcov_138 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_138_0, pch_138_1, pch_138_2, pch_138_3, pch_138_4, pch_138_5])

theorem proot_139 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 139) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_139_0, decode 300 e_139_1, decode 300 e_139_2, decode 300 e_139_3, decode 300 e_139_4, decode 96 e_139_5] (fun x hx => ub_bits hx) pcov_139 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_139_0, pch_139_1, pch_139_2, pch_139_3, pch_139_4, pch_139_5])

theorem proot_140 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 140) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_140_0, decode 300 e_140_1, decode 300 e_140_2, decode 300 e_140_3, decode 300 e_140_4, decode 84 e_140_5] (fun x hx => ub_bits hx) pcov_140 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_140_0, pch_140_1, pch_140_2, pch_140_3, pch_140_4, pch_140_5])

theorem proot_141 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 141) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_141_0, decode 300 e_141_1, decode 300 e_141_2, decode 300 e_141_3, decode 300 e_141_4, decode 82 e_141_5] (fun x hx => ub_bits hx) pcov_141 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_141_0, pch_141_1, pch_141_2, pch_141_3, pch_141_4, pch_141_5])

theorem proot_142 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 142) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_142_0, decode 300 e_142_1, decode 300 e_142_2, decode 300 e_142_3, decode 300 e_142_4, decode 94 e_142_5] (fun x hx => ub_bits hx) pcov_142 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_142_0, pch_142_1, pch_142_2, pch_142_3, pch_142_4, pch_142_5])

theorem proot_143 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 143) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_143_0, decode 300 e_143_1, decode 300 e_143_2, decode 300 e_143_3, decode 300 e_143_4, decode 92 e_143_5] (fun x hx => ub_bits hx) pcov_143 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_143_0, pch_143_1, pch_143_2, pch_143_3, pch_143_4, pch_143_5])

theorem proot_144 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 144) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_144_0, decode 300 e_144_1, decode 300 e_144_2, decode 300 e_144_3, decode 300 e_144_4, decode 77 e_144_5] (fun x hx => ub_bits hx) pcov_144 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_144_0, pch_144_1, pch_144_2, pch_144_3, pch_144_4, pch_144_5])

theorem proot_145 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 145) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_145_0, decode 300 e_145_1, decode 300 e_145_2, decode 300 e_145_3, decode 300 e_145_4, decode 86 e_145_5] (fun x hx => ub_bits hx) pcov_145 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_145_0, pch_145_1, pch_145_2, pch_145_3, pch_145_4, pch_145_5])

theorem proot_146 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 146) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_146_0, decode 300 e_146_1, decode 300 e_146_2, decode 300 e_146_3, decode 300 e_146_4, decode 95 e_146_5] (fun x hx => ub_bits hx) pcov_146 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_146_0, pch_146_1, pch_146_2, pch_146_3, pch_146_4, pch_146_5])

theorem proot_147 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 147) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_147_0, decode 300 e_147_1, decode 300 e_147_2, decode 300 e_147_3, decode 300 e_147_4, decode 92 e_147_5] (fun x hx => ub_bits hx) pcov_147 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_147_0, pch_147_1, pch_147_2, pch_147_3, pch_147_4, pch_147_5])

theorem proot_148 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 148) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_148_0, decode 300 e_148_1, decode 300 e_148_2, decode 300 e_148_3, decode 300 e_148_4, decode 78 e_148_5] (fun x hx => ub_bits hx) pcov_148 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_148_0, pch_148_1, pch_148_2, pch_148_3, pch_148_4, pch_148_5])

theorem proot_149 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 149) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_149_0, decode 300 e_149_1, decode 300 e_149_2, decode 300 e_149_3, decode 300 e_149_4, decode 86 e_149_5] (fun x hx => ub_bits hx) pcov_149 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_149_0, pch_149_1, pch_149_2, pch_149_3, pch_149_4, pch_149_5])

theorem proot_150 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 150) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_150_0, decode 300 e_150_1, decode 300 e_150_2, decode 300 e_150_3, decode 300 e_150_4, decode 72 e_150_5] (fun x hx => ub_bits hx) pcov_150 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_150_0, pch_150_1, pch_150_2, pch_150_3, pch_150_4, pch_150_5])

theorem proot_151 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 151) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_151_0, decode 300 e_151_1, decode 300 e_151_2, decode 300 e_151_3, decode 300 e_151_4, decode 83 e_151_5] (fun x hx => ub_bits hx) pcov_151 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_151_0, pch_151_1, pch_151_2, pch_151_3, pch_151_4, pch_151_5])

theorem proot_152 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 152) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_152_0, decode 300 e_152_1, decode 300 e_152_2, decode 300 e_152_3, decode 300 e_152_4, decode 98 e_152_5] (fun x hx => ub_bits hx) pcov_152 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_152_0, pch_152_1, pch_152_2, pch_152_3, pch_152_4, pch_152_5])

theorem proot_153 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 153) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_153_0, decode 300 e_153_1, decode 300 e_153_2, decode 300 e_153_3, decode 300 e_153_4, decode 87 e_153_5] (fun x hx => ub_bits hx) pcov_153 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_153_0, pch_153_1, pch_153_2, pch_153_3, pch_153_4, pch_153_5])

theorem proot_154 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 154) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_154_0, decode 300 e_154_1, decode 300 e_154_2, decode 300 e_154_3, decode 300 e_154_4, decode 78 e_154_5] (fun x hx => ub_bits hx) pcov_154 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_154_0, pch_154_1, pch_154_2, pch_154_3, pch_154_4, pch_154_5])

theorem proot_155 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 155) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_155_0, decode 300 e_155_1, decode 300 e_155_2, decode 300 e_155_3, decode 300 e_155_4, decode 79 e_155_5] (fun x hx => ub_bits hx) pcov_155 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_155_0, pch_155_1, pch_155_2, pch_155_3, pch_155_4, pch_155_5])

theorem proot_156 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 156) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_156_0, decode 300 e_156_1, decode 300 e_156_2, decode 300 e_156_3, decode 300 e_156_4, decode 72 e_156_5] (fun x hx => ub_bits hx) pcov_156 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_156_0, pch_156_1, pch_156_2, pch_156_3, pch_156_4, pch_156_5])

theorem proot_157 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 157) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_157_0, decode 300 e_157_1, decode 300 e_157_2, decode 300 e_157_3, decode 300 e_157_4, decode 83 e_157_5] (fun x hx => ub_bits hx) pcov_157 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_157_0, pch_157_1, pch_157_2, pch_157_3, pch_157_4, pch_157_5])

theorem proot_158 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 158) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_158_0, decode 300 e_158_1, decode 300 e_158_2, decode 300 e_158_3, decode 300 e_158_4, decode 92 e_158_5] (fun x hx => ub_bits hx) pcov_158 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_158_0, pch_158_1, pch_158_2, pch_158_3, pch_158_4, pch_158_5])

theorem proot_159 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 159) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_159_0, decode 300 e_159_1, decode 300 e_159_2, decode 300 e_159_3, decode 300 e_159_4, decode 87 e_159_5] (fun x hx => ub_bits hx) pcov_159 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_159_0, pch_159_1, pch_159_2, pch_159_3, pch_159_4, pch_159_5])

theorem proot_160 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 160) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_160_0, decode 300 e_160_1, decode 300 e_160_2, decode 300 e_160_3, decode 300 e_160_4, decode 75 e_160_5] (fun x hx => ub_bits hx) pcov_160 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_160_0, pch_160_1, pch_160_2, pch_160_3, pch_160_4, pch_160_5])

theorem proot_161 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 161) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_161_0, decode 300 e_161_1, decode 300 e_161_2, decode 300 e_161_3, decode 300 e_161_4, decode 77 e_161_5] (fun x hx => ub_bits hx) pcov_161 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_161_0, pch_161_1, pch_161_2, pch_161_3, pch_161_4, pch_161_5])

theorem proot_162 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 162) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_162_0, decode 300 e_162_1, decode 300 e_162_2, decode 300 e_162_3, decode 300 e_162_4, decode 76 e_162_5] (fun x hx => ub_bits hx) pcov_162 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_162_0, pch_162_1, pch_162_2, pch_162_3, pch_162_4, pch_162_5])

theorem proot_163 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 163) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_163_0, decode 300 e_163_1, decode 300 e_163_2, decode 300 e_163_3, decode 300 e_163_4, decode 80 e_163_5] (fun x hx => ub_bits hx) pcov_163 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_163_0, pch_163_1, pch_163_2, pch_163_3, pch_163_4, pch_163_5])

theorem proot_164 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 164) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_164_0, decode 300 e_164_1, decode 300 e_164_2, decode 300 e_164_3, decode 300 e_164_4, decode 94 e_164_5] (fun x hx => ub_bits hx) pcov_164 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_164_0, pch_164_1, pch_164_2, pch_164_3, pch_164_4, pch_164_5])

theorem proot_165 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 165) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_165_0, decode 300 e_165_1, decode 300 e_165_2, decode 300 e_165_3, decode 300 e_165_4, decode 90 e_165_5] (fun x hx => ub_bits hx) pcov_165 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_165_0, pch_165_1, pch_165_2, pch_165_3, pch_165_4, pch_165_5])

theorem proot_166 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 166) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_166_0, decode 300 e_166_1, decode 300 e_166_2, decode 300 e_166_3, decode 300 e_166_4, decode 78 e_166_5] (fun x hx => ub_bits hx) pcov_166 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_166_0, pch_166_1, pch_166_2, pch_166_3, pch_166_4, pch_166_5])

theorem proot_167 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 167) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_167_0, decode 300 e_167_1, decode 300 e_167_2, decode 300 e_167_3, decode 300 e_167_4, decode 81 e_167_5] (fun x hx => ub_bits hx) pcov_167 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_167_0, pch_167_1, pch_167_2, pch_167_3, pch_167_4, pch_167_5])

theorem proot_168 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 168) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_168_0, decode 300 e_168_1, decode 300 e_168_2, decode 300 e_168_3, decode 300 e_168_4, decode 81 e_168_5] (fun x hx => ub_bits hx) pcov_168 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_168_0, pch_168_1, pch_168_2, pch_168_3, pch_168_4, pch_168_5])

theorem proot_169 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 169) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_169_0, decode 300 e_169_1, decode 300 e_169_2, decode 300 e_169_3, decode 300 e_169_4, decode 72 e_169_5] (fun x hx => ub_bits hx) pcov_169 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_169_0, pch_169_1, pch_169_2, pch_169_3, pch_169_4, pch_169_5])

theorem proot_170 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 170) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_170_0, decode 300 e_170_1, decode 300 e_170_2, decode 300 e_170_3, decode 300 e_170_4, decode 92 e_170_5] (fun x hx => ub_bits hx) pcov_170 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_170_0, pch_170_1, pch_170_2, pch_170_3, pch_170_4, pch_170_5])

theorem proot_171 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 171) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_171_0, decode 300 e_171_1, decode 300 e_171_2, decode 300 e_171_3, decode 300 e_171_4, decode 89 e_171_5] (fun x hx => ub_bits hx) pcov_171 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_171_0, pch_171_1, pch_171_2, pch_171_3, pch_171_4, pch_171_5])

theorem proot_172 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 172) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_172_0, decode 300 e_172_1, decode 300 e_172_2, decode 300 e_172_3, decode 300 e_172_4, decode 77 e_172_5] (fun x hx => ub_bits hx) pcov_172 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_172_0, pch_172_1, pch_172_2, pch_172_3, pch_172_4, pch_172_5])

theorem proot_173 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 173) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_173_0, decode 300 e_173_1, decode 300 e_173_2, decode 300 e_173_3, decode 300 e_173_4, decode 76 e_173_5] (fun x hx => ub_bits hx) pcov_173 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_173_0, pch_173_1, pch_173_2, pch_173_3, pch_173_4, pch_173_5])

theorem proot_174 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 174) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_174_0, decode 300 e_174_1, decode 300 e_174_2, decode 300 e_174_3, decode 300 e_174_4, decode 77 e_174_5] (fun x hx => ub_bits hx) pcov_174 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_174_0, pch_174_1, pch_174_2, pch_174_3, pch_174_4, pch_174_5])

theorem proot_175 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 175) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_175_0, decode 300 e_175_1, decode 300 e_175_2, decode 300 e_175_3, decode 300 e_175_4, decode 71 e_175_5] (fun x hx => ub_bits hx) pcov_175 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_175_0, pch_175_1, pch_175_2, pch_175_3, pch_175_4, pch_175_5])

theorem proot_176 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 176) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_176_0, decode 300 e_176_1, decode 300 e_176_2, decode 300 e_176_3, decode 300 e_176_4, decode 85 e_176_5] (fun x hx => ub_bits hx) pcov_176 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_176_0, pch_176_1, pch_176_2, pch_176_3, pch_176_4, pch_176_5])

theorem proot_177 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 177) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_177_0, decode 300 e_177_1, decode 300 e_177_2, decode 300 e_177_3, decode 300 e_177_4, decode 88 e_177_5] (fun x hx => ub_bits hx) pcov_177 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_177_0, pch_177_1, pch_177_2, pch_177_3, pch_177_4, pch_177_5])

theorem proot_178 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 178) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_178_0, decode 300 e_178_1, decode 300 e_178_2, decode 300 e_178_3, decode 300 e_178_4, decode 76 e_178_5] (fun x hx => ub_bits hx) pcov_178 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_178_0, pch_178_1, pch_178_2, pch_178_3, pch_178_4, pch_178_5])

theorem proot_179 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 179) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_179_0, decode 300 e_179_1, decode 300 e_179_2, decode 300 e_179_3, decode 300 e_179_4, decode 72 e_179_5] (fun x hx => ub_bits hx) pcov_179 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_179_0, pch_179_1, pch_179_2, pch_179_3, pch_179_4, pch_179_5])

theorem proot_180 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 180) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_180_0, decode 300 e_180_1, decode 300 e_180_2, decode 300 e_180_3, decode 300 e_180_4, decode 78 e_180_5] (fun x hx => ub_bits hx) pcov_180 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_180_0, pch_180_1, pch_180_2, pch_180_3, pch_180_4, pch_180_5])

theorem proot_181 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 181) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_181_0, decode 300 e_181_1, decode 300 e_181_2, decode 300 e_181_3, decode 300 e_181_4, decode 71 e_181_5] (fun x hx => ub_bits hx) pcov_181 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_181_0, pch_181_1, pch_181_2, pch_181_3, pch_181_4, pch_181_5])

theorem proot_182 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 182) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_182_0, decode 300 e_182_1, decode 300 e_182_2, decode 300 e_182_3, decode 300 e_182_4, decode 81 e_182_5] (fun x hx => ub_bits hx) pcov_182 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_182_0, pch_182_1, pch_182_2, pch_182_3, pch_182_4, pch_182_5])

theorem proot_183 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 183) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_183_0, decode 300 e_183_1, decode 300 e_183_2, decode 300 e_183_3, decode 300 e_183_4, decode 81 e_183_5] (fun x hx => ub_bits hx) pcov_183 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_183_0, pch_183_1, pch_183_2, pch_183_3, pch_183_4, pch_183_5])

theorem proot_184 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 184) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_184_0, decode 300 e_184_1, decode 300 e_184_2, decode 300 e_184_3, decode 300 e_184_4, decode 75 e_184_5] (fun x hx => ub_bits hx) pcov_184 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_184_0, pch_184_1, pch_184_2, pch_184_3, pch_184_4, pch_184_5])

theorem proot_185 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 185) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_185_0, decode 300 e_185_1, decode 300 e_185_2, decode 300 e_185_3, decode 300 e_185_4, decode 81 e_185_5] (fun x hx => ub_bits hx) pcov_185 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_185_0, pch_185_1, pch_185_2, pch_185_3, pch_185_4, pch_185_5])

theorem proot_186 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 186) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_186_0, decode 300 e_186_1, decode 300 e_186_2, decode 300 e_186_3, decode 300 e_186_4, decode 81 e_186_5] (fun x hx => ub_bits hx) pcov_186 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_186_0, pch_186_1, pch_186_2, pch_186_3, pch_186_4, pch_186_5])

theorem proot_187 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 187) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_187_0, decode 300 e_187_1, decode 300 e_187_2, decode 300 e_187_3, decode 300 e_187_4, decode 71 e_187_5] (fun x hx => ub_bits hx) pcov_187 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_187_0, pch_187_1, pch_187_2, pch_187_3, pch_187_4, pch_187_5])

theorem proot_188 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 188) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_188_0, decode 300 e_188_1, decode 300 e_188_2, decode 300 e_188_3, decode 300 e_188_4, decode 77 e_188_5] (fun x hx => ub_bits hx) pcov_188 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_188_0, pch_188_1, pch_188_2, pch_188_3, pch_188_4, pch_188_5])

theorem proot_189 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 189) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_189_0, decode 300 e_189_1, decode 300 e_189_2, decode 300 e_189_3, decode 300 e_189_4, decode 81 e_189_5] (fun x hx => ub_bits hx) pcov_189 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_189_0, pch_189_1, pch_189_2, pch_189_3, pch_189_4, pch_189_5])

theorem proot_190 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 190) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_190_0, decode 300 e_190_1, decode 300 e_190_2, decode 300 e_190_3, decode 300 e_190_4, decode 75 e_190_5] (fun x hx => ub_bits hx) pcov_190 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_190_0, pch_190_1, pch_190_2, pch_190_3, pch_190_4, pch_190_5])

theorem proot_191 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 191) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_191_0, decode 300 e_191_1, decode 300 e_191_2, decode 300 e_191_3, decode 300 e_191_4, decode 81 e_191_5] (fun x hx => ub_bits hx) pcov_191 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_191_0, pch_191_1, pch_191_2, pch_191_3, pch_191_4, pch_191_5])

theorem proot_192 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 192) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_192_0, decode 300 e_192_1, decode 300 e_192_2, decode 300 e_192_3, decode 300 e_192_4, decode 82 e_192_5] (fun x hx => ub_bits hx) pcov_192 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_192_0, pch_192_1, pch_192_2, pch_192_3, pch_192_4, pch_192_5])

theorem proot_193 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 193) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_193_0, decode 300 e_193_1, decode 300 e_193_2, decode 300 e_193_3, decode 300 e_193_4, decode 94 e_193_5] (fun x hx => ub_bits hx) pcov_193 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_193_0, pch_193_1, pch_193_2, pch_193_3, pch_193_4, pch_193_5])

theorem proot_194 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 194) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_194_0, decode 300 e_194_1, decode 300 e_194_2, decode 300 e_194_3, decode 300 e_194_4, decode 73 e_194_5] (fun x hx => ub_bits hx) pcov_194 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_194_0, pch_194_1, pch_194_2, pch_194_3, pch_194_4, pch_194_5])

theorem proot_195 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 195) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_195_0, decode 300 e_195_1, decode 300 e_195_2, decode 300 e_195_3, decode 300 e_195_4, decode 76 e_195_5] (fun x hx => ub_bits hx) pcov_195 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_195_0, pch_195_1, pch_195_2, pch_195_3, pch_195_4, pch_195_5])

theorem proot_196 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 196) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_196_0, decode 300 e_196_1, decode 300 e_196_2, decode 300 e_196_3, decode 300 e_196_4, decode 91 e_196_5] (fun x hx => ub_bits hx) pcov_196 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_196_0, pch_196_1, pch_196_2, pch_196_3, pch_196_4, pch_196_5])

theorem proot_197 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 197) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_197_0, decode 300 e_197_1, decode 300 e_197_2, decode 300 e_197_3, decode 300 e_197_4, decode 88 e_197_5] (fun x hx => ub_bits hx) pcov_197 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_197_0, pch_197_1, pch_197_2, pch_197_3, pch_197_4, pch_197_5])

theorem proot_198 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 198) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_198_0, decode 300 e_198_1, decode 300 e_198_2, decode 300 e_198_3, decode 300 e_198_4, decode 86 e_198_5] (fun x hx => ub_bits hx) pcov_198 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_198_0, pch_198_1, pch_198_2, pch_198_3, pch_198_4, pch_198_5])

theorem proot_199 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 199) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_199_0, decode 300 e_199_1, decode 300 e_199_2, decode 300 e_199_3, decode 300 e_199_4, decode 94 e_199_5] (fun x hx => ub_bits hx) pcov_199 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_199_0, pch_199_1, pch_199_2, pch_199_3, pch_199_4, pch_199_5])

theorem proot_200 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 200) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_200_0, decode 300 e_200_1, decode 300 e_200_2, decode 300 e_200_3, decode 300 e_200_4, decode 71 e_200_5] (fun x hx => ub_bits hx) pcov_200 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_200_0, pch_200_1, pch_200_2, pch_200_3, pch_200_4, pch_200_5])

theorem proot_201 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 201) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_201_0, decode 300 e_201_1, decode 300 e_201_2, decode 300 e_201_3, decode 300 e_201_4, decode 77 e_201_5] (fun x hx => ub_bits hx) pcov_201 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_201_0, pch_201_1, pch_201_2, pch_201_3, pch_201_4, pch_201_5])

theorem proot_202 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 202) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_202_0, decode 300 e_202_1, decode 300 e_202_2, decode 300 e_202_3, decode 300 e_202_4, decode 92 e_202_5] (fun x hx => ub_bits hx) pcov_202 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_202_0, pch_202_1, pch_202_2, pch_202_3, pch_202_4, pch_202_5])

theorem proot_203 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 203) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_203_0, decode 300 e_203_1, decode 300 e_203_2, decode 300 e_203_3, decode 300 e_203_4, decode 88 e_203_5] (fun x hx => ub_bits hx) pcov_203 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_203_0, pch_203_1, pch_203_2, pch_203_3, pch_203_4, pch_203_5])

theorem proot_204 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 204) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_204_0, decode 300 e_204_1, decode 300 e_204_2, decode 300 e_204_3, decode 300 e_204_4, decode 86 e_204_5] (fun x hx => ub_bits hx) pcov_204 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_204_0, pch_204_1, pch_204_2, pch_204_3, pch_204_4, pch_204_5])

theorem proot_205 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 205) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_205_0, decode 300 e_205_1, decode 300 e_205_2, decode 300 e_205_3, decode 300 e_205_4, decode 95 e_205_5] (fun x hx => ub_bits hx) pcov_205 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_205_0, pch_205_1, pch_205_2, pch_205_3, pch_205_4, pch_205_5])

theorem proot_206 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 206) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_206_0, decode 300 e_206_1, decode 300 e_206_2, decode 300 e_206_3, decode 300 e_206_4, decode 71 e_206_5] (fun x hx => ub_bits hx) pcov_206 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_206_0, pch_206_1, pch_206_2, pch_206_3, pch_206_4, pch_206_5])

theorem proot_207 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 207) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_207_0, decode 300 e_207_1, decode 300 e_207_2, decode 300 e_207_3, decode 300 e_207_4, decode 82 e_207_5] (fun x hx => ub_bits hx) pcov_207 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_207_0, pch_207_1, pch_207_2, pch_207_3, pch_207_4, pch_207_5])

theorem proot_208 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 208) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_208_0, decode 300 e_208_1, decode 300 e_208_2, decode 300 e_208_3, decode 300 e_208_4, decode 92 e_208_5] (fun x hx => ub_bits hx) pcov_208 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_208_0, pch_208_1, pch_208_2, pch_208_3, pch_208_4, pch_208_5])

theorem proot_209 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 209) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_209_0, decode 300 e_209_1, decode 300 e_209_2, decode 300 e_209_3, decode 300 e_209_4, decode 88 e_209_5] (fun x hx => ub_bits hx) pcov_209 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_209_0, pch_209_1, pch_209_2, pch_209_3, pch_209_4, pch_209_5])

theorem proot_210 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 210) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_210_0, decode 300 e_210_1, decode 300 e_210_2, decode 300 e_210_3, decode 300 e_210_4, decode 94 e_210_5] (fun x hx => ub_bits hx) pcov_210 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_210_0, pch_210_1, pch_210_2, pch_210_3, pch_210_4, pch_210_5])

theorem proot_211 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 211) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_211_0, decode 300 e_211_1, decode 300 e_211_2, decode 300 e_211_3, decode 300 e_211_4, decode 102 e_211_5] (fun x hx => ub_bits hx) pcov_211 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_211_0, pch_211_1, pch_211_2, pch_211_3, pch_211_4, pch_211_5])

theorem proot_212 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 212) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_212_0, decode 300 e_212_1, decode 300 e_212_2, decode 300 e_212_3, decode 300 e_212_4, decode 79 e_212_5] (fun x hx => ub_bits hx) pcov_212 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_212_0, pch_212_1, pch_212_2, pch_212_3, pch_212_4, pch_212_5])

theorem proot_213 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 213) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_213_0, decode 300 e_213_1, decode 300 e_213_2, decode 300 e_213_3, decode 300 e_213_4, decode 82 e_213_5] (fun x hx => ub_bits hx) pcov_213 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_213_0, pch_213_1, pch_213_2, pch_213_3, pch_213_4, pch_213_5])

theorem proot_214 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 214) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_214_0, decode 300 e_214_1, decode 300 e_214_2, decode 300 e_214_3, decode 300 e_214_4, decode 100 e_214_5] (fun x hx => ub_bits hx) pcov_214 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_214_0, pch_214_1, pch_214_2, pch_214_3, pch_214_4, pch_214_5])

theorem proot_215 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 215) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_215_0, decode 300 e_215_1, decode 300 e_215_2, decode 300 e_215_3, decode 300 e_215_4, decode 93 e_215_5] (fun x hx => ub_bits hx) pcov_215 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_215_0, pch_215_1, pch_215_2, pch_215_3, pch_215_4, pch_215_5])

theorem proot_216 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 216) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_216_0, decode 300 e_216_1, decode 300 e_216_2, decode 300 e_216_3, decode 300 e_216_4, decode 76 e_216_5] (fun x hx => ub_bits hx) pcov_216 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_216_0, pch_216_1, pch_216_2, pch_216_3, pch_216_4, pch_216_5])

theorem proot_217 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 217) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_217_0, decode 300 e_217_1, decode 300 e_217_2, decode 300 e_217_3, decode 300 e_217_4, decode 92 e_217_5] (fun x hx => ub_bits hx) pcov_217 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_217_0, pch_217_1, pch_217_2, pch_217_3, pch_217_4, pch_217_5])

theorem proot_218 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 218) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_218_0, decode 300 e_218_1, decode 300 e_218_2, decode 300 e_218_3, decode 300 e_218_4, decode 101 e_218_5] (fun x hx => ub_bits hx) pcov_218 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_218_0, pch_218_1, pch_218_2, pch_218_3, pch_218_4, pch_218_5])

theorem proot_219 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 219) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_219_0, decode 300 e_219_1, decode 300 e_219_2, decode 300 e_219_3, decode 300 e_219_4, decode 75 e_219_5] (fun x hx => ub_bits hx) pcov_219 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_219_0, pch_219_1, pch_219_2, pch_219_3, pch_219_4, pch_219_5])

theorem proot_220 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 220) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_220_0, decode 300 e_220_1, decode 300 e_220_2, decode 300 e_220_3, decode 300 e_220_4, decode 90 e_220_5] (fun x hx => ub_bits hx) pcov_220 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_220_0, pch_220_1, pch_220_2, pch_220_3, pch_220_4, pch_220_5])

theorem proot_221 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 221) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_221_0, decode 300 e_221_1, decode 300 e_221_2, decode 300 e_221_3, decode 300 e_221_4, decode 79 e_221_5] (fun x hx => ub_bits hx) pcov_221 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_221_0, pch_221_1, pch_221_2, pch_221_3, pch_221_4, pch_221_5])

theorem proot_222 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 222) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_222_0, decode 300 e_222_1, decode 300 e_222_2, decode 300 e_222_3, decode 300 e_222_4, decode 71 e_222_5] (fun x hx => ub_bits hx) pcov_222 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_222_0, pch_222_1, pch_222_2, pch_222_3, pch_222_4, pch_222_5])

theorem proot_223 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 223) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_223_0, decode 300 e_223_1, decode 300 e_223_2, decode 300 e_223_3, decode 300 e_223_4, decode 90 e_223_5] (fun x hx => ub_bits hx) pcov_223 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_223_0, pch_223_1, pch_223_2, pch_223_3, pch_223_4, pch_223_5])

theorem proot_224 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 224) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_224_0, decode 300 e_224_1, decode 300 e_224_2, decode 300 e_224_3, decode 300 e_224_4, decode 91 e_224_5] (fun x hx => ub_bits hx) pcov_224 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_224_0, pch_224_1, pch_224_2, pch_224_3, pch_224_4, pch_224_5])

theorem proot_225 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 225) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_225_0, decode 300 e_225_1, decode 300 e_225_2, decode 300 e_225_3, decode 300 e_225_4, decode 75 e_225_5] (fun x hx => ub_bits hx) pcov_225 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_225_0, pch_225_1, pch_225_2, pch_225_3, pch_225_4, pch_225_5])

theorem proot_226 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 226) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_226_0, decode 300 e_226_1, decode 300 e_226_2, decode 300 e_226_3, decode 300 e_226_4, decode 82 e_226_5] (fun x hx => ub_bits hx) pcov_226 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_226_0, pch_226_1, pch_226_2, pch_226_3, pch_226_4, pch_226_5])

theorem proot_227 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 227) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_227_0, decode 300 e_227_1, decode 300 e_227_2, decode 300 e_227_3, decode 300 e_227_4, decode 83 e_227_5] (fun x hx => ub_bits hx) pcov_227 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_227_0, pch_227_1, pch_227_2, pch_227_3, pch_227_4, pch_227_5])

theorem proot_228 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 228) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_228_0, decode 300 e_228_1, decode 300 e_228_2, decode 300 e_228_3, decode 300 e_228_4, decode 75 e_228_5] (fun x hx => ub_bits hx) pcov_228 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_228_0, pch_228_1, pch_228_2, pch_228_3, pch_228_4, pch_228_5])

theorem proot_229 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 229) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_229_0, decode 300 e_229_1, decode 300 e_229_2, decode 300 e_229_3, decode 300 e_229_4, decode 83 e_229_5] (fun x hx => ub_bits hx) pcov_229 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_229_0, pch_229_1, pch_229_2, pch_229_3, pch_229_4, pch_229_5])

theorem proot_230 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 230) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_230_0, decode 300 e_230_1, decode 300 e_230_2, decode 300 e_230_3, decode 300 e_230_4, decode 91 e_230_5] (fun x hx => ub_bits hx) pcov_230 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_230_0, pch_230_1, pch_230_2, pch_230_3, pch_230_4, pch_230_5])

theorem proot_231 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 231) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_231_0, decode 300 e_231_1, decode 300 e_231_2, decode 300 e_231_3, decode 300 e_231_4, decode 72 e_231_5] (fun x hx => ub_bits hx) pcov_231 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_231_0, pch_231_1, pch_231_2, pch_231_3, pch_231_4, pch_231_5])

theorem proot_232 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 232) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_232_0, decode 300 e_232_1, decode 300 e_232_2, decode 300 e_232_3, decode 300 e_232_4, decode 78 e_232_5] (fun x hx => ub_bits hx) pcov_232 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_232_0, pch_232_1, pch_232_2, pch_232_3, pch_232_4, pch_232_5])

theorem proot_233 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 233) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_233_0, decode 300 e_233_1, decode 300 e_233_2, decode 300 e_233_3, decode 300 e_233_4, decode 79 e_233_5] (fun x hx => ub_bits hx) pcov_233 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_233_0, pch_233_1, pch_233_2, pch_233_3, pch_233_4, pch_233_5])

theorem proot_234 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 234) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_234_0, decode 300 e_234_1, decode 300 e_234_2, decode 300 e_234_3, decode 300 e_234_4, decode 77 e_234_5] (fun x hx => ub_bits hx) pcov_234 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_234_0, pch_234_1, pch_234_2, pch_234_3, pch_234_4, pch_234_5])

theorem proot_235 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 235) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_235_0, decode 300 e_235_1, decode 300 e_235_2, decode 300 e_235_3, decode 300 e_235_4, decode 80 e_235_5] (fun x hx => ub_bits hx) pcov_235 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_235_0, pch_235_1, pch_235_2, pch_235_3, pch_235_4, pch_235_5])

theorem proot_236 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 236) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_236_0, decode 300 e_236_1, decode 300 e_236_2, decode 300 e_236_3, decode 300 e_236_4, decode 93 e_236_5] (fun x hx => ub_bits hx) pcov_236 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_236_0, pch_236_1, pch_236_2, pch_236_3, pch_236_4, pch_236_5])

theorem proot_237 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 237) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_237_0, decode 300 e_237_1, decode 300 e_237_2, decode 300 e_237_3, decode 300 e_237_4, decode 77 e_237_5] (fun x hx => ub_bits hx) pcov_237 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_237_0, pch_237_1, pch_237_2, pch_237_3, pch_237_4, pch_237_5])

theorem proot_238 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 238) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_238_0, decode 300 e_238_1, decode 300 e_238_2, decode 300 e_238_3, decode 300 e_238_4, decode 76 e_238_5] (fun x hx => ub_bits hx) pcov_238 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_238_0, pch_238_1, pch_238_2, pch_238_3, pch_238_4, pch_238_5])

theorem proot_239 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 239) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_239_0, decode 300 e_239_1, decode 300 e_239_2, decode 300 e_239_3, decode 300 e_239_4, decode 79 e_239_5] (fun x hx => ub_bits hx) pcov_239 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_239_0, pch_239_1, pch_239_2, pch_239_3, pch_239_4, pch_239_5])

theorem proot_240 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 240) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_240_0, decode 300 e_240_1, decode 300 e_240_2, decode 300 e_240_3, decode 300 e_240_4, decode 79 e_240_5] (fun x hx => ub_bits hx) pcov_240 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_240_0, pch_240_1, pch_240_2, pch_240_3, pch_240_4, pch_240_5])

theorem proot_241 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 241) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_241_0, decode 300 e_241_1, decode 300 e_241_2, decode 300 e_241_3, decode 300 e_241_4, decode 73 e_241_5] (fun x hx => ub_bits hx) pcov_241 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_241_0, pch_241_1, pch_241_2, pch_241_3, pch_241_4, pch_241_5])

theorem proot_242 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 242) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_242_0, decode 300 e_242_1, decode 300 e_242_2, decode 300 e_242_3, decode 300 e_242_4, decode 92 e_242_5] (fun x hx => ub_bits hx) pcov_242 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_242_0, pch_242_1, pch_242_2, pch_242_3, pch_242_4, pch_242_5])

theorem proot_243 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 243) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_243_0, decode 300 e_243_1, decode 300 e_243_2, decode 300 e_243_3, decode 300 e_243_4, decode 94 e_243_5] (fun x hx => ub_bits hx) pcov_243 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_243_0, pch_243_1, pch_243_2, pch_243_3, pch_243_4, pch_243_5])

theorem proot_244 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 244) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_244_0, decode 300 e_244_1, decode 300 e_244_2, decode 300 e_244_3, decode 300 e_244_4, decode 73 e_244_5] (fun x hx => ub_bits hx) pcov_244 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_244_0, pch_244_1, pch_244_2, pch_244_3, pch_244_4, pch_244_5])

theorem proot_245 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 245) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_245_0, decode 300 e_245_1, decode 300 e_245_2, decode 300 e_245_3, decode 300 e_245_4, decode 84 e_245_5] (fun x hx => ub_bits hx) pcov_245 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_245_0, pch_245_1, pch_245_2, pch_245_3, pch_245_4, pch_245_5])

theorem proot_246 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 246) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_246_0, decode 300 e_246_1, decode 300 e_246_2, decode 300 e_246_3, decode 300 e_246_4, decode 80 e_246_5] (fun x hx => ub_bits hx) pcov_246 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_246_0, pch_246_1, pch_246_2, pch_246_3, pch_246_4, pch_246_5])

theorem proot_247 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 247) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_247_0, decode 300 e_247_1, decode 300 e_247_2, decode 300 e_247_3, decode 300 e_247_4, decode 73 e_247_5] (fun x hx => ub_bits hx) pcov_247 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_247_0, pch_247_1, pch_247_2, pch_247_3, pch_247_4, pch_247_5])

theorem proot_248 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 248) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_248_0, decode 300 e_248_1, decode 300 e_248_2, decode 300 e_248_3, decode 300 e_248_4, decode 94 e_248_5] (fun x hx => ub_bits hx) pcov_248 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_248_0, pch_248_1, pch_248_2, pch_248_3, pch_248_4, pch_248_5])

theorem proot_249 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 249) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_249_0, decode 300 e_249_1, decode 300 e_249_2, decode 300 e_249_3, decode 300 e_249_4, decode 96 e_249_5] (fun x hx => ub_bits hx) pcov_249 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_249_0, pch_249_1, pch_249_2, pch_249_3, pch_249_4, pch_249_5])

theorem proot_250 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 250) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_250_0, decode 300 e_250_1, decode 300 e_250_2, decode 300 e_250_3, decode 300 e_250_4, decode 73 e_250_5] (fun x hx => ub_bits hx) pcov_250 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_250_0, pch_250_1, pch_250_2, pch_250_3, pch_250_4, pch_250_5])

theorem proot_251 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) : Claim (UB 251) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 e_251_0, decode 300 e_251_1, decode 300 e_251_2, decode 300 e_251_3, decode 300 e_251_4, decode 85 e_251_5] (fun x hx => ub_bits hx) pcov_251 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pch_251_0, pch_251_1, pch_251_2, pch_251_3, pch_251_4, pch_251_5])

end LRC.O7U5
