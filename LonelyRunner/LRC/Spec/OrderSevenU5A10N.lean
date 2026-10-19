import LonelyRunner.LRC.Spec.OrderSevenU5SoundN
import LonelyRunner.LRC.Spec.OrderSevenU5C100N
import LonelyRunner.LRC.Spec.OrderSevenU5C101N
import LonelyRunner.LRC.Spec.OrderSevenU5C102N
import LonelyRunner.LRC.Spec.OrderSevenU5C103N
import LonelyRunner.LRC.Spec.OrderSevenU5C104N
import LonelyRunner.LRC.Spec.OrderSevenU5C105N
import LonelyRunner.LRC.Spec.OrderSevenU5C106N
import LonelyRunner.LRC.Spec.OrderSevenU5C107N
import LonelyRunner.LRC.Spec.OrderSevenU5C108N
import LonelyRunner.LRC.Spec.OrderSevenU5C109N

set_option maxRecDepth 100000

namespace LRC.O7U5

theorem root_6710 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6710) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6710_0, decode 300 d_6710_1, decode 300 d_6710_2, decode 300 d_6710_3, decode 300 d_6710_4, decode 300 d_6710_5, decode 300 d_6710_6, decode 141 d_6710_7] (fun x hx => bits_full_and hx) cov_6710 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6710_0, ch_6710_1, ch_6710_2, ch_6710_3, ch_6710_4, ch_6710_5, ch_6710_6, ch_6710_7])

theorem root_6711 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6711) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6711_0, decode 300 d_6711_1, decode 300 d_6711_2, decode 300 d_6711_3, decode 300 d_6711_4, decode 300 d_6711_5, decode 300 d_6711_6, decode 142 d_6711_7] (fun x hx => bits_full_and hx) cov_6711 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6711_0, ch_6711_1, ch_6711_2, ch_6711_3, ch_6711_4, ch_6711_5, ch_6711_6, ch_6711_7])

theorem root_6712 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6712) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6712_0, decode 300 d_6712_1, decode 300 d_6712_2, decode 300 d_6712_3, decode 300 d_6712_4, decode 300 d_6712_5, decode 300 d_6712_6, decode 142 d_6712_7] (fun x hx => bits_full_and hx) cov_6712 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6712_0, ch_6712_1, ch_6712_2, ch_6712_3, ch_6712_4, ch_6712_5, ch_6712_6, ch_6712_7])

theorem root_6713 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6713) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6713_0, decode 300 d_6713_1, decode 300 d_6713_2, decode 300 d_6713_3, decode 300 d_6713_4, decode 300 d_6713_5, decode 300 d_6713_6, decode 142 d_6713_7] (fun x hx => bits_full_and hx) cov_6713 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6713_0, ch_6713_1, ch_6713_2, ch_6713_3, ch_6713_4, ch_6713_5, ch_6713_6, ch_6713_7])

theorem root_6718 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6718) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6718_0, decode 300 d_6718_1, decode 300 d_6718_2, decode 300 d_6718_3, decode 300 d_6718_4, decode 300 d_6718_5, decode 300 d_6718_6, decode 141 d_6718_7] (fun x hx => bits_full_and hx) cov_6718 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6718_0, ch_6718_1, ch_6718_2, ch_6718_3, ch_6718_4, ch_6718_5, ch_6718_6, ch_6718_7])

theorem root_6726 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6726) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6726_0, decode 300 d_6726_1, decode 300 d_6726_2, decode 300 d_6726_3, decode 300 d_6726_4, decode 300 d_6726_5, decode 300 d_6726_6, decode 141 d_6726_7] (fun x hx => bits_full_and hx) cov_6726 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6726_0, ch_6726_1, ch_6726_2, ch_6726_3, ch_6726_4, ch_6726_5, ch_6726_6, ch_6726_7])

theorem root_6735 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6735) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6735_0, decode 300 d_6735_1, decode 300 d_6735_2, decode 300 d_6735_3, decode 300 d_6735_4, decode 300 d_6735_5, decode 300 d_6735_6, decode 141 d_6735_7] (fun x hx => bits_full_and hx) cov_6735 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6735_0, ch_6735_1, ch_6735_2, ch_6735_3, ch_6735_4, ch_6735_5, ch_6735_6, ch_6735_7])

theorem root_6736 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6736) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6736_0, decode 300 d_6736_1, decode 300 d_6736_2, decode 300 d_6736_3, decode 300 d_6736_4, decode 300 d_6736_5, decode 300 d_6736_6, decode 161 d_6736_7] (fun x hx => bits_full_and hx) cov_6736 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6736_0, ch_6736_1, ch_6736_2, ch_6736_3, ch_6736_4, ch_6736_5, ch_6736_6, ch_6736_7])

theorem root_6737 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6737) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6737_0, decode 300 d_6737_1, decode 300 d_6737_2, decode 300 d_6737_3, decode 300 d_6737_4, decode 300 d_6737_5, decode 300 d_6737_6, decode 161 d_6737_7] (fun x hx => bits_full_and hx) cov_6737 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6737_0, ch_6737_1, ch_6737_2, ch_6737_3, ch_6737_4, ch_6737_5, ch_6737_6, ch_6737_7])

theorem root_6747 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6747) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6747_0, decode 300 d_6747_1, decode 300 d_6747_2, decode 300 d_6747_3, decode 300 d_6747_4, decode 300 d_6747_5, decode 300 d_6747_6, decode 141 d_6747_7] (fun x hx => bits_full_and hx) cov_6747 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6747_0, ch_6747_1, ch_6747_2, ch_6747_3, ch_6747_4, ch_6747_5, ch_6747_6, ch_6747_7])

theorem root_6748 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6748) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6748_0, decode 300 d_6748_1, decode 300 d_6748_2, decode 300 d_6748_3, decode 300 d_6748_4, decode 300 d_6748_5, decode 300 d_6748_6, decode 141 d_6748_7] (fun x hx => bits_full_and hx) cov_6748 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6748_0, ch_6748_1, ch_6748_2, ch_6748_3, ch_6748_4, ch_6748_5, ch_6748_6, ch_6748_7])

theorem root_6757 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6757) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6757_0, decode 300 d_6757_1, decode 300 d_6757_2, decode 300 d_6757_3, decode 300 d_6757_4, decode 300 d_6757_5, decode 107 d_6757_6] (fun x hx => bits_full_and hx) cov_6757 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6757_0, ch_6757_1, ch_6757_2, ch_6757_3, ch_6757_4, ch_6757_5, ch_6757_6])

theorem root_6758 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6758) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6758_0, decode 300 d_6758_1, decode 300 d_6758_2, decode 300 d_6758_3, decode 300 d_6758_4, decode 300 d_6758_5, decode 51 d_6758_6] (fun x hx => bits_full_and hx) cov_6758 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6758_0, ch_6758_1, ch_6758_2, ch_6758_3, ch_6758_4, ch_6758_5, ch_6758_6])

theorem root_6759 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6759) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6759_0, decode 300 d_6759_1, decode 300 d_6759_2, decode 300 d_6759_3, decode 300 d_6759_4, decode 300 d_6759_5, decode 300 d_6759_6, decode 141 d_6759_7] (fun x hx => bits_full_and hx) cov_6759 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6759_0, ch_6759_1, ch_6759_2, ch_6759_3, ch_6759_4, ch_6759_5, ch_6759_6, ch_6759_7])

theorem root_6763 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6763) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6763_0, decode 300 d_6763_1, decode 300 d_6763_2, decode 300 d_6763_3, decode 300 d_6763_4, decode 300 d_6763_5, decode 300 d_6763_6, decode 141 d_6763_7] (fun x hx => bits_full_and hx) cov_6763 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6763_0, ch_6763_1, ch_6763_2, ch_6763_3, ch_6763_4, ch_6763_5, ch_6763_6, ch_6763_7])

theorem root_6764 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6764) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6764_0, decode 300 d_6764_1, decode 300 d_6764_2, decode 300 d_6764_3, decode 300 d_6764_4, decode 300 d_6764_5, decode 300 d_6764_6, decode 142 d_6764_7] (fun x hx => bits_full_and hx) cov_6764 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6764_0, ch_6764_1, ch_6764_2, ch_6764_3, ch_6764_4, ch_6764_5, ch_6764_6, ch_6764_7])

theorem root_6770 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6770) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6770_0, decode 300 d_6770_1, decode 300 d_6770_2, decode 300 d_6770_3, decode 300 d_6770_4, decode 300 d_6770_5, decode 300 d_6770_6, decode 141 d_6770_7] (fun x hx => bits_full_and hx) cov_6770 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6770_0, ch_6770_1, ch_6770_2, ch_6770_3, ch_6770_4, ch_6770_5, ch_6770_6, ch_6770_7])

theorem root_6771 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6771) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6771_0, decode 300 d_6771_1, decode 300 d_6771_2, decode 300 d_6771_3, decode 300 d_6771_4, decode 300 d_6771_5, decode 300 d_6771_6, decode 142 d_6771_7] (fun x hx => bits_full_and hx) cov_6771 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6771_0, ch_6771_1, ch_6771_2, ch_6771_3, ch_6771_4, ch_6771_5, ch_6771_6, ch_6771_7])

theorem root_6772 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6772) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6772_0, decode 300 d_6772_1, decode 300 d_6772_2, decode 300 d_6772_3, decode 300 d_6772_4, decode 300 d_6772_5, decode 300 d_6772_6, decode 141 d_6772_7] (fun x hx => bits_full_and hx) cov_6772 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6772_0, ch_6772_1, ch_6772_2, ch_6772_3, ch_6772_4, ch_6772_5, ch_6772_6, ch_6772_7])

theorem roots_100_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_100, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_100, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6710 hB hC hCl hCB, root_6711 hB hC hCl hCB, root_6712 hB hC hCl hCB, root_6713 hB hC hCl hCB, root_6718 hB hC hCl hCB, root_6726 hB hC hCl hCB, root_6735 hB hC hCl hCB, root_6736 hB hC hCl hCB, root_6737 hB hC hCl hCB, root_6747 hB hC hCl hCB, root_6748 hB hC hCl hCB, root_6757 hB hC hCl hCB, root_6758 hB hC hCl hCB, root_6759 hB hC hCl hCB, root_6763 hB hC hCl hCB, root_6764 hB hC hCl hCB, root_6770 hB hC hCl hCB, root_6771 hB hC hCl hCB, root_6772 hB hC hCl hCB]

theorem root_6776 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6776) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6776_0, decode 300 d_6776_1, decode 300 d_6776_2, decode 300 d_6776_3, decode 300 d_6776_4, decode 300 d_6776_5, decode 300 d_6776_6, decode 141 d_6776_7] (fun x hx => bits_full_and hx) cov_6776 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6776_0, ch_6776_1, ch_6776_2, ch_6776_3, ch_6776_4, ch_6776_5, ch_6776_6, ch_6776_7])

theorem root_6784 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6784) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6784_0, decode 300 d_6784_1, decode 300 d_6784_2, decode 300 d_6784_3, decode 300 d_6784_4, decode 300 d_6784_5, decode 300 d_6784_6, decode 141 d_6784_7] (fun x hx => bits_full_and hx) cov_6784 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6784_0, ch_6784_1, ch_6784_2, ch_6784_3, ch_6784_4, ch_6784_5, ch_6784_6, ch_6784_7])

theorem root_6785 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6785) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6785_0, decode 300 d_6785_1, decode 300 d_6785_2, decode 300 d_6785_3, decode 300 d_6785_4, decode 300 d_6785_5, decode 300 d_6785_6, decode 142 d_6785_7] (fun x hx => bits_full_and hx) cov_6785 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6785_0, ch_6785_1, ch_6785_2, ch_6785_3, ch_6785_4, ch_6785_5, ch_6785_6, ch_6785_7])

theorem root_6794 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6794) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6794_0, decode 300 d_6794_1, decode 300 d_6794_2, decode 300 d_6794_3, decode 300 d_6794_4, decode 300 d_6794_5, decode 300 d_6794_6, decode 141 d_6794_7] (fun x hx => bits_full_and hx) cov_6794 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6794_0, ch_6794_1, ch_6794_2, ch_6794_3, ch_6794_4, ch_6794_5, ch_6794_6, ch_6794_7])

theorem root_6795 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6795) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6795_0, decode 300 d_6795_1, decode 300 d_6795_2, decode 300 d_6795_3, decode 300 d_6795_4, decode 300 d_6795_5, decode 300 d_6795_6, decode 141 d_6795_7] (fun x hx => bits_full_and hx) cov_6795 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6795_0, ch_6795_1, ch_6795_2, ch_6795_3, ch_6795_4, ch_6795_5, ch_6795_6, ch_6795_7])

theorem root_6797 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6797) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6797_0, decode 300 d_6797_1, decode 300 d_6797_2, decode 300 d_6797_3, decode 300 d_6797_4, decode 300 d_6797_5, decode 300 d_6797_6, decode 142 d_6797_7] (fun x hx => bits_full_and hx) cov_6797 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6797_0, ch_6797_1, ch_6797_2, ch_6797_3, ch_6797_4, ch_6797_5, ch_6797_6, ch_6797_7])

theorem root_6798 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6798) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6798_0, decode 300 d_6798_1, decode 300 d_6798_2, decode 300 d_6798_3, decode 300 d_6798_4, decode 300 d_6798_5, decode 300 d_6798_6, decode 141 d_6798_7] (fun x hx => bits_full_and hx) cov_6798 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6798_0, ch_6798_1, ch_6798_2, ch_6798_3, ch_6798_4, ch_6798_5, ch_6798_6, ch_6798_7])

theorem root_6799 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6799) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6799_0, decode 300 d_6799_1, decode 300 d_6799_2, decode 300 d_6799_3, decode 300 d_6799_4, decode 300 d_6799_5, decode 300 d_6799_6, decode 142 d_6799_7] (fun x hx => bits_full_and hx) cov_6799 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6799_0, ch_6799_1, ch_6799_2, ch_6799_3, ch_6799_4, ch_6799_5, ch_6799_6, ch_6799_7])

theorem root_6803 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6803) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6803_0, decode 300 d_6803_1, decode 300 d_6803_2, decode 300 d_6803_3, decode 300 d_6803_4, decode 300 d_6803_5, decode 300 d_6803_6, decode 141 d_6803_7] (fun x hx => bits_full_and hx) cov_6803 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6803_0, ch_6803_1, ch_6803_2, ch_6803_3, ch_6803_4, ch_6803_5, ch_6803_6, ch_6803_7])

theorem root_6804 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6804) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6804_0, decode 300 d_6804_1, decode 300 d_6804_2, decode 300 d_6804_3, decode 300 d_6804_4, decode 300 d_6804_5, decode 300 d_6804_6, decode 141 d_6804_7] (fun x hx => bits_full_and hx) cov_6804 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6804_0, ch_6804_1, ch_6804_2, ch_6804_3, ch_6804_4, ch_6804_5, ch_6804_6, ch_6804_7])

theorem root_6806 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6806) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6806_0, decode 300 d_6806_1, decode 300 d_6806_2, decode 300 d_6806_3, decode 300 d_6806_4, decode 300 d_6806_5, decode 300 d_6806_6, decode 142 d_6806_7] (fun x hx => bits_full_and hx) cov_6806 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6806_0, ch_6806_1, ch_6806_2, ch_6806_3, ch_6806_4, ch_6806_5, ch_6806_6, ch_6806_7])

theorem root_6807 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6807) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6807_0, decode 300 d_6807_1, decode 300 d_6807_2, decode 300 d_6807_3, decode 300 d_6807_4, decode 300 d_6807_5, decode 300 d_6807_6, decode 142 d_6807_7] (fun x hx => bits_full_and hx) cov_6807 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6807_0, ch_6807_1, ch_6807_2, ch_6807_3, ch_6807_4, ch_6807_5, ch_6807_6, ch_6807_7])

theorem root_6814 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6814) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6814_0, decode 300 d_6814_1, decode 300 d_6814_2, decode 300 d_6814_3, decode 300 d_6814_4, decode 300 d_6814_5, decode 300 d_6814_6, decode 142 d_6814_7] (fun x hx => bits_full_and hx) cov_6814 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6814_0, ch_6814_1, ch_6814_2, ch_6814_3, ch_6814_4, ch_6814_5, ch_6814_6, ch_6814_7])

theorem root_6815 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6815) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6815_0, decode 300 d_6815_1, decode 300 d_6815_2, decode 300 d_6815_3, decode 300 d_6815_4, decode 300 d_6815_5, decode 300 d_6815_6, decode 142 d_6815_7] (fun x hx => bits_full_and hx) cov_6815 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6815_0, ch_6815_1, ch_6815_2, ch_6815_3, ch_6815_4, ch_6815_5, ch_6815_6, ch_6815_7])

theorem root_6816 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6816) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6816_0, decode 300 d_6816_1, decode 300 d_6816_2, decode 300 d_6816_3, decode 300 d_6816_4, decode 300 d_6816_5, decode 300 d_6816_6, decode 142 d_6816_7] (fun x hx => bits_full_and hx) cov_6816 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6816_0, ch_6816_1, ch_6816_2, ch_6816_3, ch_6816_4, ch_6816_5, ch_6816_6, ch_6816_7])

theorem root_6817 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6817) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6817_0, decode 300 d_6817_1, decode 300 d_6817_2, decode 300 d_6817_3, decode 300 d_6817_4, decode 300 d_6817_5, decode 300 d_6817_6, decode 141 d_6817_7] (fun x hx => bits_full_and hx) cov_6817 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6817_0, ch_6817_1, ch_6817_2, ch_6817_3, ch_6817_4, ch_6817_5, ch_6817_6, ch_6817_7])

theorem root_6820 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6820) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6820_0, decode 300 d_6820_1, decode 300 d_6820_2, decode 300 d_6820_3, decode 300 d_6820_4, decode 300 d_6820_5, decode 300 d_6820_6, decode 56 d_6820_7] (fun x hx => bits_full_and hx) cov_6820 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6820_0, ch_6820_1, ch_6820_2, ch_6820_3, ch_6820_4, ch_6820_5, ch_6820_6, ch_6820_7])

theorem root_6823 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6823) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6823_0, decode 300 d_6823_1, decode 300 d_6823_2, decode 300 d_6823_3, decode 300 d_6823_4, decode 257 d_6823_5] (fun x hx => bits_full_and hx) cov_6823 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6823_0, ch_6823_1, ch_6823_2, ch_6823_3, ch_6823_4, ch_6823_5])

theorem root_6824 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6824) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6824_0, decode 300 d_6824_1, decode 300 d_6824_2, decode 300 d_6824_3, decode 300 d_6824_4, decode 257 d_6824_5] (fun x hx => bits_full_and hx) cov_6824 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6824_0, ch_6824_1, ch_6824_2, ch_6824_3, ch_6824_4, ch_6824_5])

theorem roots_101_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_101, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_101, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6776 hB hC hCl hCB, root_6784 hB hC hCl hCB, root_6785 hB hC hCl hCB, root_6794 hB hC hCl hCB, root_6795 hB hC hCl hCB, root_6797 hB hC hCl hCB, root_6798 hB hC hCl hCB, root_6799 hB hC hCl hCB, root_6803 hB hC hCl hCB, root_6804 hB hC hCl hCB, root_6806 hB hC hCl hCB, root_6807 hB hC hCl hCB, root_6814 hB hC hCl hCB, root_6815 hB hC hCl hCB, root_6816 hB hC hCl hCB, root_6817 hB hC hCl hCB, root_6820 hB hC hCl hCB, root_6823 hB hC hCl hCB, root_6824 hB hC hCl hCB]

theorem root_6826 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6826) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6826_0, decode 300 d_6826_1, decode 300 d_6826_2, decode 300 d_6826_3, decode 300 d_6826_4, decode 300 d_6826_5, decode 187 d_6826_6] (fun x hx => bits_full_and hx) cov_6826 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6826_0, ch_6826_1, ch_6826_2, ch_6826_3, ch_6826_4, ch_6826_5, ch_6826_6])

theorem root_6827 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6827) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6827_0, decode 300 d_6827_1, decode 300 d_6827_2, decode 300 d_6827_3, decode 300 d_6827_4, decode 300 d_6827_5, decode 187 d_6827_6] (fun x hx => bits_full_and hx) cov_6827 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6827_0, ch_6827_1, ch_6827_2, ch_6827_3, ch_6827_4, ch_6827_5, ch_6827_6])

theorem root_6832 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6832) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6832_0, decode 300 d_6832_1, decode 300 d_6832_2, decode 300 d_6832_3, decode 300 d_6832_4, decode 257 d_6832_5] (fun x hx => bits_full_and hx) cov_6832 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6832_0, ch_6832_1, ch_6832_2, ch_6832_3, ch_6832_4, ch_6832_5])

theorem root_6834 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6834) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6834_0, decode 300 d_6834_1, decode 300 d_6834_2, decode 300 d_6834_3, decode 300 d_6834_4, decode 292 d_6834_5] (fun x hx => bits_full_and hx) cov_6834 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6834_0, ch_6834_1, ch_6834_2, ch_6834_3, ch_6834_4, ch_6834_5])

theorem root_6835 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6835) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6835_0, decode 300 d_6835_1, decode 300 d_6835_2, decode 300 d_6835_3, decode 300 d_6835_4, decode 292 d_6835_5] (fun x hx => bits_full_and hx) cov_6835 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6835_0, ch_6835_1, ch_6835_2, ch_6835_3, ch_6835_4, ch_6835_5])

theorem root_6841 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6841) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6841_0, decode 300 d_6841_1, decode 300 d_6841_2, decode 300 d_6841_3, decode 300 d_6841_4, decode 300 d_6841_5, decode 192 d_6841_6] (fun x hx => bits_full_and hx) cov_6841 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6841_0, ch_6841_1, ch_6841_2, ch_6841_3, ch_6841_4, ch_6841_5, ch_6841_6])

theorem root_6842 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6842) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6842_0, decode 300 d_6842_1, decode 300 d_6842_2, decode 300 d_6842_3, decode 300 d_6842_4, decode 300 d_6842_5, decode 192 d_6842_6] (fun x hx => bits_full_and hx) cov_6842 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6842_0, ch_6842_1, ch_6842_2, ch_6842_3, ch_6842_4, ch_6842_5, ch_6842_6])

theorem root_6843 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6843) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6843_0, decode 300 d_6843_1, decode 300 d_6843_2, decode 300 d_6843_3, decode 300 d_6843_4, decode 300 d_6843_5, decode 192 d_6843_6] (fun x hx => bits_full_and hx) cov_6843 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6843_0, ch_6843_1, ch_6843_2, ch_6843_3, ch_6843_4, ch_6843_5, ch_6843_6])

theorem root_6846 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6846) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6846_0, decode 300 d_6846_1, decode 300 d_6846_2, decode 300 d_6846_3, decode 300 d_6846_4, decode 213 d_6846_5] (fun x hx => bits_full_and hx) cov_6846 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6846_0, ch_6846_1, ch_6846_2, ch_6846_3, ch_6846_4, ch_6846_5])

theorem root_6848 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6848) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6848_0, decode 300 d_6848_1, decode 300 d_6848_2, decode 300 d_6848_3, decode 300 d_6848_4, decode 300 d_6848_5, decode 87 d_6848_6] (fun x hx => bits_full_and hx) cov_6848 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6848_0, ch_6848_1, ch_6848_2, ch_6848_3, ch_6848_4, ch_6848_5, ch_6848_6])

theorem root_6849 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6849) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6849_0, decode 300 d_6849_1, decode 300 d_6849_2, decode 300 d_6849_3, decode 300 d_6849_4, decode 292 d_6849_5] (fun x hx => bits_full_and hx) cov_6849 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6849_0, ch_6849_1, ch_6849_2, ch_6849_3, ch_6849_4, ch_6849_5])

theorem root_6850 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6850) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6850_0, decode 300 d_6850_1, decode 300 d_6850_2, decode 300 d_6850_3, decode 300 d_6850_4, decode 292 d_6850_5] (fun x hx => bits_full_and hx) cov_6850 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6850_0, ch_6850_1, ch_6850_2, ch_6850_3, ch_6850_4, ch_6850_5])

theorem root_6858 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6858) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6858_0, decode 300 d_6858_1, decode 300 d_6858_2, decode 300 d_6858_3, decode 300 d_6858_4, decode 300 d_6858_5, decode 72 d_6858_6] (fun x hx => bits_full_and hx) cov_6858 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6858_0, ch_6858_1, ch_6858_2, ch_6858_3, ch_6858_4, ch_6858_5, ch_6858_6])

theorem root_6865 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6865) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6865_0, decode 300 d_6865_1, decode 300 d_6865_2, decode 300 d_6865_3, decode 300 d_6865_4, decode 300 d_6865_5, decode 75 d_6865_6] (fun x hx => bits_full_and hx) cov_6865 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6865_0, ch_6865_1, ch_6865_2, ch_6865_3, ch_6865_4, ch_6865_5, ch_6865_6])

theorem root_6871 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6871) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6871_0, decode 300 d_6871_1, decode 300 d_6871_2, decode 300 d_6871_3, decode 300 d_6871_4, decode 300 d_6871_5, decode 71 d_6871_6] (fun x hx => bits_full_and hx) cov_6871 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6871_0, ch_6871_1, ch_6871_2, ch_6871_3, ch_6871_4, ch_6871_5, ch_6871_6])

theorem root_6876 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6876) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6876_0, decode 300 d_6876_1, decode 300 d_6876_2, decode 300 d_6876_3, decode 300 d_6876_4, decode 300 d_6876_5, decode 60 d_6876_6] (fun x hx => bits_full_and hx) cov_6876 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6876_0, ch_6876_1, ch_6876_2, ch_6876_3, ch_6876_4, ch_6876_5, ch_6876_6])

theorem root_6886 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6886) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6886_0, decode 300 d_6886_1, decode 300 d_6886_2, decode 300 d_6886_3, decode 300 d_6886_4, decode 300 d_6886_5, decode 300 d_6886_6, decode 158 d_6886_7] (fun x hx => bits_full_and hx) cov_6886 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6886_0, ch_6886_1, ch_6886_2, ch_6886_3, ch_6886_4, ch_6886_5, ch_6886_6, ch_6886_7])

theorem root_6887 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6887) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6887_0, decode 300 d_6887_1, decode 300 d_6887_2, decode 300 d_6887_3, decode 300 d_6887_4, decode 300 d_6887_5, decode 300 d_6887_6, decode 141 d_6887_7] (fun x hx => bits_full_and hx) cov_6887 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6887_0, ch_6887_1, ch_6887_2, ch_6887_3, ch_6887_4, ch_6887_5, ch_6887_6, ch_6887_7])

theorem root_6888 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6888) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6888_0, decode 300 d_6888_1, decode 300 d_6888_2, decode 300 d_6888_3, decode 300 d_6888_4, decode 300 d_6888_5, decode 300 d_6888_6, decode 158 d_6888_7] (fun x hx => bits_full_and hx) cov_6888 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6888_0, ch_6888_1, ch_6888_2, ch_6888_3, ch_6888_4, ch_6888_5, ch_6888_6, ch_6888_7])

theorem root_6894 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6894) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6894_0, decode 300 d_6894_1, decode 300 d_6894_2, decode 300 d_6894_3, decode 300 d_6894_4, decode 300 d_6894_5, decode 300 d_6894_6, decode 141 d_6894_7] (fun x hx => bits_full_and hx) cov_6894 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6894_0, ch_6894_1, ch_6894_2, ch_6894_3, ch_6894_4, ch_6894_5, ch_6894_6, ch_6894_7])

theorem root_6895 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6895) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6895_0, decode 300 d_6895_1, decode 300 d_6895_2, decode 300 d_6895_3, decode 300 d_6895_4, decode 300 d_6895_5, decode 300 d_6895_6, decode 141 d_6895_7] (fun x hx => bits_full_and hx) cov_6895 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6895_0, ch_6895_1, ch_6895_2, ch_6895_3, ch_6895_4, ch_6895_5, ch_6895_6, ch_6895_7])

theorem roots_102_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_102, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_102, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6826 hB hC hCl hCB, root_6827 hB hC hCl hCB, root_6832 hB hC hCl hCB, root_6834 hB hC hCl hCB, root_6835 hB hC hCl hCB, root_6841 hB hC hCl hCB, root_6842 hB hC hCl hCB, root_6843 hB hC hCl hCB, root_6846 hB hC hCl hCB, root_6848 hB hC hCl hCB, root_6849 hB hC hCl hCB, root_6850 hB hC hCl hCB, root_6858 hB hC hCl hCB, root_6865 hB hC hCl hCB, root_6871 hB hC hCl hCB, root_6876 hB hC hCl hCB, root_6886 hB hC hCl hCB, root_6887 hB hC hCl hCB, root_6888 hB hC hCl hCB, root_6894 hB hC hCl hCB, root_6895 hB hC hCl hCB]

theorem root_6896 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6896) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6896_0, decode 300 d_6896_1, decode 300 d_6896_2, decode 300 d_6896_3, decode 300 d_6896_4, decode 300 d_6896_5, decode 300 d_6896_6, decode 158 d_6896_7] (fun x hx => bits_full_and hx) cov_6896 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6896_0, ch_6896_1, ch_6896_2, ch_6896_3, ch_6896_4, ch_6896_5, ch_6896_6, ch_6896_7])

theorem root_6897 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6897) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6897_0, decode 300 d_6897_1, decode 300 d_6897_2, decode 300 d_6897_3, decode 300 d_6897_4, decode 300 d_6897_5, decode 300 d_6897_6, decode 158 d_6897_7] (fun x hx => bits_full_and hx) cov_6897 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6897_0, ch_6897_1, ch_6897_2, ch_6897_3, ch_6897_4, ch_6897_5, ch_6897_6, ch_6897_7])

theorem root_6898 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6898) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6898_0, decode 300 d_6898_1, decode 300 d_6898_2, decode 300 d_6898_3, decode 300 d_6898_4, decode 300 d_6898_5, decode 300 d_6898_6, decode 158 d_6898_7] (fun x hx => bits_full_and hx) cov_6898 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6898_0, ch_6898_1, ch_6898_2, ch_6898_3, ch_6898_4, ch_6898_5, ch_6898_6, ch_6898_7])

theorem root_6905 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6905) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6905_0, decode 300 d_6905_1, decode 300 d_6905_2, decode 300 d_6905_3, decode 300 d_6905_4, decode 300 d_6905_5, decode 300 d_6905_6, decode 141 d_6905_7] (fun x hx => bits_full_and hx) cov_6905 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6905_0, ch_6905_1, ch_6905_2, ch_6905_3, ch_6905_4, ch_6905_5, ch_6905_6, ch_6905_7])

theorem root_6906 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6906) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6906_0, decode 300 d_6906_1, decode 300 d_6906_2, decode 300 d_6906_3, decode 300 d_6906_4, decode 300 d_6906_5, decode 300 d_6906_6, decode 141 d_6906_7] (fun x hx => bits_full_and hx) cov_6906 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6906_0, ch_6906_1, ch_6906_2, ch_6906_3, ch_6906_4, ch_6906_5, ch_6906_6, ch_6906_7])

theorem root_6907 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6907) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6907_0, decode 300 d_6907_1, decode 300 d_6907_2, decode 300 d_6907_3, decode 300 d_6907_4, decode 300 d_6907_5, decode 300 d_6907_6, decode 141 d_6907_7] (fun x hx => bits_full_and hx) cov_6907 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6907_0, ch_6907_1, ch_6907_2, ch_6907_3, ch_6907_4, ch_6907_5, ch_6907_6, ch_6907_7])

theorem root_6908 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6908) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6908_0, decode 300 d_6908_1, decode 300 d_6908_2, decode 300 d_6908_3, decode 300 d_6908_4, decode 300 d_6908_5, decode 300 d_6908_6, decode 158 d_6908_7] (fun x hx => bits_full_and hx) cov_6908 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6908_0, ch_6908_1, ch_6908_2, ch_6908_3, ch_6908_4, ch_6908_5, ch_6908_6, ch_6908_7])

theorem root_6909 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6909) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6909_0, decode 300 d_6909_1, decode 300 d_6909_2, decode 300 d_6909_3, decode 300 d_6909_4, decode 300 d_6909_5, decode 104 d_6909_6] (fun x hx => bits_full_and hx) cov_6909 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6909_0, ch_6909_1, ch_6909_2, ch_6909_3, ch_6909_4, ch_6909_5, ch_6909_6])

theorem root_6923 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6923) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6923_0, decode 300 d_6923_1, decode 300 d_6923_2, decode 300 d_6923_3, decode 300 d_6923_4, decode 300 d_6923_5, decode 300 d_6923_6, decode 141 d_6923_7] (fun x hx => bits_full_and hx) cov_6923 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6923_0, ch_6923_1, ch_6923_2, ch_6923_3, ch_6923_4, ch_6923_5, ch_6923_6, ch_6923_7])

theorem root_6924 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6924) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6924_0, decode 300 d_6924_1, decode 300 d_6924_2, decode 300 d_6924_3, decode 300 d_6924_4, decode 300 d_6924_5, decode 300 d_6924_6, decode 142 d_6924_7] (fun x hx => bits_full_and hx) cov_6924 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6924_0, ch_6924_1, ch_6924_2, ch_6924_3, ch_6924_4, ch_6924_5, ch_6924_6, ch_6924_7])

theorem root_6928 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6928) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6928_0, decode 300 d_6928_1, decode 300 d_6928_2, decode 300 d_6928_3, decode 300 d_6928_4, decode 300 d_6928_5, decode 300 d_6928_6, decode 142 d_6928_7] (fun x hx => bits_full_and hx) cov_6928 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6928_0, ch_6928_1, ch_6928_2, ch_6928_3, ch_6928_4, ch_6928_5, ch_6928_6, ch_6928_7])

theorem root_6929 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6929) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6929_0, decode 300 d_6929_1, decode 300 d_6929_2, decode 300 d_6929_3, decode 300 d_6929_4, decode 300 d_6929_5, decode 300 d_6929_6, decode 142 d_6929_7] (fun x hx => bits_full_and hx) cov_6929 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6929_0, ch_6929_1, ch_6929_2, ch_6929_3, ch_6929_4, ch_6929_5, ch_6929_6, ch_6929_7])

theorem root_6930 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6930) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6930_0, decode 300 d_6930_1, decode 300 d_6930_2, decode 300 d_6930_3, decode 300 d_6930_4, decode 300 d_6930_5, decode 300 d_6930_6, decode 141 d_6930_7] (fun x hx => bits_full_and hx) cov_6930 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6930_0, ch_6930_1, ch_6930_2, ch_6930_3, ch_6930_4, ch_6930_5, ch_6930_6, ch_6930_7])

theorem root_6938 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6938) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6938_0, decode 300 d_6938_1, decode 300 d_6938_2, decode 300 d_6938_3, decode 300 d_6938_4, decode 300 d_6938_5, decode 300 d_6938_6, decode 142 d_6938_7] (fun x hx => bits_full_and hx) cov_6938 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6938_0, ch_6938_1, ch_6938_2, ch_6938_3, ch_6938_4, ch_6938_5, ch_6938_6, ch_6938_7])

theorem root_6939 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6939) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6939_0, decode 300 d_6939_1, decode 300 d_6939_2, decode 300 d_6939_3, decode 300 d_6939_4, decode 300 d_6939_5, decode 300 d_6939_6, decode 141 d_6939_7] (fun x hx => bits_full_and hx) cov_6939 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6939_0, ch_6939_1, ch_6939_2, ch_6939_3, ch_6939_4, ch_6939_5, ch_6939_6, ch_6939_7])

theorem root_6940 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6940) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6940_0, decode 300 d_6940_1, decode 300 d_6940_2, decode 300 d_6940_3, decode 300 d_6940_4, decode 300 d_6940_5, decode 300 d_6940_6, decode 141 d_6940_7] (fun x hx => bits_full_and hx) cov_6940 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6940_0, ch_6940_1, ch_6940_2, ch_6940_3, ch_6940_4, ch_6940_5, ch_6940_6, ch_6940_7])

theorem root_6941 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6941) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6941_0, decode 300 d_6941_1, decode 300 d_6941_2, decode 300 d_6941_3, decode 300 d_6941_4, decode 300 d_6941_5, decode 300 d_6941_6, decode 141 d_6941_7] (fun x hx => bits_full_and hx) cov_6941 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6941_0, ch_6941_1, ch_6941_2, ch_6941_3, ch_6941_4, ch_6941_5, ch_6941_6, ch_6941_7])

theorem root_6946 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6946) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6946_0, decode 300 d_6946_1, decode 300 d_6946_2, decode 300 d_6946_3, decode 300 d_6946_4, decode 300 d_6946_5, decode 6 d_6946_6] (fun x hx => bits_full_and hx) cov_6946 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6946_0, ch_6946_1, ch_6946_2, ch_6946_3, ch_6946_4, ch_6946_5, ch_6946_6])

theorem root_6947 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6947) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6947_0, decode 300 d_6947_1, decode 300 d_6947_2, decode 300 d_6947_3, decode 300 d_6947_4, decode 300 d_6947_5, decode 6 d_6947_6] (fun x hx => bits_full_and hx) cov_6947 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6947_0, ch_6947_1, ch_6947_2, ch_6947_3, ch_6947_4, ch_6947_5, ch_6947_6])

theorem roots_103_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_103, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_103, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6896 hB hC hCl hCB, root_6897 hB hC hCl hCB, root_6898 hB hC hCl hCB, root_6905 hB hC hCl hCB, root_6906 hB hC hCl hCB, root_6907 hB hC hCl hCB, root_6908 hB hC hCl hCB, root_6909 hB hC hCl hCB, root_6923 hB hC hCl hCB, root_6924 hB hC hCl hCB, root_6928 hB hC hCl hCB, root_6929 hB hC hCl hCB, root_6930 hB hC hCl hCB, root_6938 hB hC hCl hCB, root_6939 hB hC hCl hCB, root_6940 hB hC hCl hCB, root_6941 hB hC hCl hCB, root_6946 hB hC hCl hCB, root_6947 hB hC hCl hCB]

theorem root_6955 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6955) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6955_0, decode 300 d_6955_1, decode 300 d_6955_2, decode 300 d_6955_3, decode 300 d_6955_4, decode 300 d_6955_5, decode 137 d_6955_6] (fun x hx => bits_full_and hx) cov_6955 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6955_0, ch_6955_1, ch_6955_2, ch_6955_3, ch_6955_4, ch_6955_5, ch_6955_6])

theorem root_6956 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6956) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6956_0, decode 300 d_6956_1, decode 300 d_6956_2, decode 300 d_6956_3, decode 300 d_6956_4, decode 300 d_6956_5, decode 137 d_6956_6] (fun x hx => bits_full_and hx) cov_6956 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6956_0, ch_6956_1, ch_6956_2, ch_6956_3, ch_6956_4, ch_6956_5, ch_6956_6])

theorem root_6957 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6957) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6957_0, decode 300 d_6957_1, decode 300 d_6957_2, decode 300 d_6957_3, decode 300 d_6957_4, decode 300 d_6957_5, decode 137 d_6957_6] (fun x hx => bits_full_and hx) cov_6957 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6957_0, ch_6957_1, ch_6957_2, ch_6957_3, ch_6957_4, ch_6957_5, ch_6957_6])

theorem root_6964 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6964) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6964_0, decode 300 d_6964_1, decode 300 d_6964_2, decode 300 d_6964_3, decode 300 d_6964_4, decode 300 d_6964_5, decode 59 d_6964_6] (fun x hx => bits_full_and hx) cov_6964 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6964_0, ch_6964_1, ch_6964_2, ch_6964_3, ch_6964_4, ch_6964_5, ch_6964_6])

theorem root_6967 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6967) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6967_0, decode 300 d_6967_1, decode 300 d_6967_2, decode 300 d_6967_3, decode 300 d_6967_4, decode 300 d_6967_5, decode 39 d_6967_6] (fun x hx => bits_full_and hx) cov_6967 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6967_0, ch_6967_1, ch_6967_2, ch_6967_3, ch_6967_4, ch_6967_5, ch_6967_6])

theorem root_6971 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6971) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6971_0, decode 300 d_6971_1, decode 300 d_6971_2, decode 300 d_6971_3, decode 300 d_6971_4, decode 300 d_6971_5, decode 12 d_6971_6] (fun x hx => bits_full_and hx) cov_6971 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6971_0, ch_6971_1, ch_6971_2, ch_6971_3, ch_6971_4, ch_6971_5, ch_6971_6])

theorem root_6973 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6973) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6973_0, decode 300 d_6973_1, decode 300 d_6973_2, decode 300 d_6973_3, decode 300 d_6973_4, decode 300 d_6973_5, decode 39 d_6973_6] (fun x hx => bits_full_and hx) cov_6973 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6973_0, ch_6973_1, ch_6973_2, ch_6973_3, ch_6973_4, ch_6973_5, ch_6973_6])

theorem root_6975 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6975) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6975_0, decode 300 d_6975_1, decode 300 d_6975_2, decode 300 d_6975_3, decode 300 d_6975_4, decode 300 d_6975_5, decode 39 d_6975_6] (fun x hx => bits_full_and hx) cov_6975 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6975_0, ch_6975_1, ch_6975_2, ch_6975_3, ch_6975_4, ch_6975_5, ch_6975_6])

theorem root_6978 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6978) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6978_0, decode 300 d_6978_1, decode 300 d_6978_2, decode 300 d_6978_3, decode 300 d_6978_4, decode 261 d_6978_5] (fun x hx => bits_full_and hx) cov_6978 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6978_0, ch_6978_1, ch_6978_2, ch_6978_3, ch_6978_4, ch_6978_5])

theorem root_6985 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6985) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6985_0, decode 300 d_6985_1, decode 300 d_6985_2, decode 300 d_6985_3, decode 300 d_6985_4, decode 300 d_6985_5, decode 300 d_6985_6, decode 142 d_6985_7] (fun x hx => bits_full_and hx) cov_6985 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6985_0, ch_6985_1, ch_6985_2, ch_6985_3, ch_6985_4, ch_6985_5, ch_6985_6, ch_6985_7])

theorem root_6986 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6986) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6986_0, decode 300 d_6986_1, decode 300 d_6986_2, decode 300 d_6986_3, decode 300 d_6986_4, decode 300 d_6986_5, decode 300 d_6986_6, decode 142 d_6986_7] (fun x hx => bits_full_and hx) cov_6986 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6986_0, ch_6986_1, ch_6986_2, ch_6986_3, ch_6986_4, ch_6986_5, ch_6986_6, ch_6986_7])

theorem root_6987 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6987) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6987_0, decode 300 d_6987_1, decode 300 d_6987_2, decode 300 d_6987_3, decode 300 d_6987_4, decode 300 d_6987_5, decode 300 d_6987_6, decode 142 d_6987_7] (fun x hx => bits_full_and hx) cov_6987 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6987_0, ch_6987_1, ch_6987_2, ch_6987_3, ch_6987_4, ch_6987_5, ch_6987_6, ch_6987_7])

theorem root_6988 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6988) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6988_0, decode 300 d_6988_1, decode 300 d_6988_2, decode 300 d_6988_3, decode 300 d_6988_4, decode 300 d_6988_5, decode 300 d_6988_6, decode 142 d_6988_7] (fun x hx => bits_full_and hx) cov_6988 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6988_0, ch_6988_1, ch_6988_2, ch_6988_3, ch_6988_4, ch_6988_5, ch_6988_6, ch_6988_7])

theorem root_6989 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6989) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6989_0, decode 300 d_6989_1, decode 300 d_6989_2, decode 300 d_6989_3, decode 300 d_6989_4, decode 300 d_6989_5, decode 300 d_6989_6, decode 141 d_6989_7] (fun x hx => bits_full_and hx) cov_6989 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6989_0, ch_6989_1, ch_6989_2, ch_6989_3, ch_6989_4, ch_6989_5, ch_6989_6, ch_6989_7])

theorem root_6990 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6990) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6990_0, decode 300 d_6990_1, decode 300 d_6990_2, decode 300 d_6990_3, decode 300 d_6990_4, decode 300 d_6990_5, decode 300 d_6990_6, decode 142 d_6990_7] (fun x hx => bits_full_and hx) cov_6990 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6990_0, ch_6990_1, ch_6990_2, ch_6990_3, ch_6990_4, ch_6990_5, ch_6990_6, ch_6990_7])

theorem root_6991 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 6991) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_6991_0, decode 300 d_6991_1, decode 300 d_6991_2, decode 300 d_6991_3, decode 300 d_6991_4, decode 300 d_6991_5, decode 300 d_6991_6, decode 142 d_6991_7] (fun x hx => bits_full_and hx) cov_6991 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_6991_0, ch_6991_1, ch_6991_2, ch_6991_3, ch_6991_4, ch_6991_5, ch_6991_6, ch_6991_7])

theorem root_7004 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7004) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7004_0, decode 300 d_7004_1, decode 300 d_7004_2, decode 300 d_7004_3, decode 300 d_7004_4, decode 300 d_7004_5, decode 300 d_7004_6, decode 141 d_7004_7] (fun x hx => bits_full_and hx) cov_7004 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7004_0, ch_7004_1, ch_7004_2, ch_7004_3, ch_7004_4, ch_7004_5, ch_7004_6, ch_7004_7])

theorem root_7005 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7005) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7005_0, decode 300 d_7005_1, decode 300 d_7005_2, decode 300 d_7005_3, decode 300 d_7005_4, decode 300 d_7005_5, decode 300 d_7005_6, decode 141 d_7005_7] (fun x hx => bits_full_and hx) cov_7005 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7005_0, ch_7005_1, ch_7005_2, ch_7005_3, ch_7005_4, ch_7005_5, ch_7005_6, ch_7005_7])

theorem root_7006 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7006) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7006_0, decode 300 d_7006_1, decode 300 d_7006_2, decode 300 d_7006_3, decode 300 d_7006_4, decode 300 d_7006_5, decode 300 d_7006_6, decode 141 d_7006_7] (fun x hx => bits_full_and hx) cov_7006 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7006_0, ch_7006_1, ch_7006_2, ch_7006_3, ch_7006_4, ch_7006_5, ch_7006_6, ch_7006_7])

theorem root_7007 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7007) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7007_0, decode 300 d_7007_1, decode 300 d_7007_2, decode 300 d_7007_3, decode 300 d_7007_4, decode 300 d_7007_5, decode 300 d_7007_6, decode 141 d_7007_7] (fun x hx => bits_full_and hx) cov_7007 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7007_0, ch_7007_1, ch_7007_2, ch_7007_3, ch_7007_4, ch_7007_5, ch_7007_6, ch_7007_7])

theorem roots_104_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_104, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_104, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_6955 hB hC hCl hCB, root_6956 hB hC hCl hCB, root_6957 hB hC hCl hCB, root_6964 hB hC hCl hCB, root_6967 hB hC hCl hCB, root_6971 hB hC hCl hCB, root_6973 hB hC hCl hCB, root_6975 hB hC hCl hCB, root_6978 hB hC hCl hCB, root_6985 hB hC hCl hCB, root_6986 hB hC hCl hCB, root_6987 hB hC hCl hCB, root_6988 hB hC hCl hCB, root_6989 hB hC hCl hCB, root_6990 hB hC hCl hCB, root_6991 hB hC hCl hCB, root_7004 hB hC hCl hCB, root_7005 hB hC hCl hCB, root_7006 hB hC hCl hCB, root_7007 hB hC hCl hCB]

theorem root_7011 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7011) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7011_0, decode 300 d_7011_1, decode 300 d_7011_2, decode 300 d_7011_3, decode 300 d_7011_4, decode 300 d_7011_5, decode 300 d_7011_6, decode 142 d_7011_7] (fun x hx => bits_full_and hx) cov_7011 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7011_0, ch_7011_1, ch_7011_2, ch_7011_3, ch_7011_4, ch_7011_5, ch_7011_6, ch_7011_7])

theorem root_7012 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7012) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7012_0, decode 300 d_7012_1, decode 300 d_7012_2, decode 300 d_7012_3, decode 300 d_7012_4, decode 300 d_7012_5, decode 300 d_7012_6, decode 142 d_7012_7] (fun x hx => bits_full_and hx) cov_7012 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7012_0, ch_7012_1, ch_7012_2, ch_7012_3, ch_7012_4, ch_7012_5, ch_7012_6, ch_7012_7])

theorem root_7014 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7014) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7014_0, decode 300 d_7014_1, decode 300 d_7014_2, decode 300 d_7014_3, decode 300 d_7014_4, decode 300 d_7014_5, decode 300 d_7014_6, decode 141 d_7014_7] (fun x hx => bits_full_and hx) cov_7014 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7014_0, ch_7014_1, ch_7014_2, ch_7014_3, ch_7014_4, ch_7014_5, ch_7014_6, ch_7014_7])

theorem root_7015 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7015) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7015_0, decode 300 d_7015_1, decode 300 d_7015_2, decode 300 d_7015_3, decode 300 d_7015_4, decode 300 d_7015_5, decode 300 d_7015_6, decode 141 d_7015_7] (fun x hx => bits_full_and hx) cov_7015 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7015_0, ch_7015_1, ch_7015_2, ch_7015_3, ch_7015_4, ch_7015_5, ch_7015_6, ch_7015_7])

theorem root_7020 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7020) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7020_0, decode 300 d_7020_1, decode 300 d_7020_2, decode 300 d_7020_3, decode 300 d_7020_4, decode 300 d_7020_5, decode 300 d_7020_6, decode 141 d_7020_7] (fun x hx => bits_full_and hx) cov_7020 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7020_0, ch_7020_1, ch_7020_2, ch_7020_3, ch_7020_4, ch_7020_5, ch_7020_6, ch_7020_7])

theorem root_7021 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7021) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7021_0, decode 300 d_7021_1, decode 300 d_7021_2, decode 300 d_7021_3, decode 300 d_7021_4, decode 300 d_7021_5, decode 300 d_7021_6, decode 141 d_7021_7] (fun x hx => bits_full_and hx) cov_7021 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7021_0, ch_7021_1, ch_7021_2, ch_7021_3, ch_7021_4, ch_7021_5, ch_7021_6, ch_7021_7])

theorem root_7022 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7022) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7022_0, decode 300 d_7022_1, decode 300 d_7022_2, decode 300 d_7022_3, decode 300 d_7022_4, decode 300 d_7022_5, decode 300 d_7022_6, decode 142 d_7022_7] (fun x hx => bits_full_and hx) cov_7022 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7022_0, ch_7022_1, ch_7022_2, ch_7022_3, ch_7022_4, ch_7022_5, ch_7022_6, ch_7022_7])

theorem root_7029 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7029) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7029_0, decode 300 d_7029_1, decode 300 d_7029_2, decode 300 d_7029_3, decode 300 d_7029_4, decode 300 d_7029_5, decode 300 d_7029_6, decode 141 d_7029_7] (fun x hx => bits_full_and hx) cov_7029 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7029_0, ch_7029_1, ch_7029_2, ch_7029_3, ch_7029_4, ch_7029_5, ch_7029_6, ch_7029_7])

theorem root_7030 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7030) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7030_0, decode 300 d_7030_1, decode 300 d_7030_2, decode 300 d_7030_3, decode 300 d_7030_4, decode 300 d_7030_5, decode 300 d_7030_6, decode 141 d_7030_7] (fun x hx => bits_full_and hx) cov_7030 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7030_0, ch_7030_1, ch_7030_2, ch_7030_3, ch_7030_4, ch_7030_5, ch_7030_6, ch_7030_7])

theorem root_7031 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7031) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7031_0, decode 300 d_7031_1, decode 300 d_7031_2, decode 300 d_7031_3, decode 300 d_7031_4, decode 300 d_7031_5, decode 300 d_7031_6, decode 142 d_7031_7] (fun x hx => bits_full_and hx) cov_7031 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7031_0, ch_7031_1, ch_7031_2, ch_7031_3, ch_7031_4, ch_7031_5, ch_7031_6, ch_7031_7])

theorem root_7033 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7033) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7033_0, decode 300 d_7033_1, decode 300 d_7033_2, decode 300 d_7033_3, decode 300 d_7033_4, decode 300 d_7033_5, decode 300 d_7033_6, decode 142 d_7033_7] (fun x hx => bits_full_and hx) cov_7033 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7033_0, ch_7033_1, ch_7033_2, ch_7033_3, ch_7033_4, ch_7033_5, ch_7033_6, ch_7033_7])

theorem root_7037 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7037) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7037_0, decode 300 d_7037_1, decode 300 d_7037_2, decode 300 d_7037_3, decode 300 d_7037_4, decode 300 d_7037_5, decode 300 d_7037_6, decode 141 d_7037_7] (fun x hx => bits_full_and hx) cov_7037 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7037_0, ch_7037_1, ch_7037_2, ch_7037_3, ch_7037_4, ch_7037_5, ch_7037_6, ch_7037_7])

theorem root_7045 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7045) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7045_0, decode 300 d_7045_1, decode 300 d_7045_2, decode 300 d_7045_3, decode 300 d_7045_4, decode 300 d_7045_5, decode 300 d_7045_6, decode 141 d_7045_7] (fun x hx => bits_full_and hx) cov_7045 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7045_0, ch_7045_1, ch_7045_2, ch_7045_3, ch_7045_4, ch_7045_5, ch_7045_6, ch_7045_7])

theorem root_7046 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7046) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7046_0, decode 300 d_7046_1, decode 300 d_7046_2, decode 300 d_7046_3, decode 300 d_7046_4, decode 300 d_7046_5, decode 300 d_7046_6, decode 141 d_7046_7] (fun x hx => bits_full_and hx) cov_7046 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7046_0, ch_7046_1, ch_7046_2, ch_7046_3, ch_7046_4, ch_7046_5, ch_7046_6, ch_7046_7])

theorem root_7047 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7047) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7047_0, decode 300 d_7047_1, decode 300 d_7047_2, decode 300 d_7047_3, decode 300 d_7047_4, decode 300 d_7047_5, decode 300 d_7047_6, decode 142 d_7047_7] (fun x hx => bits_full_and hx) cov_7047 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7047_0, ch_7047_1, ch_7047_2, ch_7047_3, ch_7047_4, ch_7047_5, ch_7047_6, ch_7047_7])

theorem root_7052 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7052) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7052_0, decode 300 d_7052_1, decode 300 d_7052_2, decode 300 d_7052_3, decode 300 d_7052_4, decode 300 d_7052_5, decode 300 d_7052_6, decode 142 d_7052_7] (fun x hx => bits_full_and hx) cov_7052 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7052_0, ch_7052_1, ch_7052_2, ch_7052_3, ch_7052_4, ch_7052_5, ch_7052_6, ch_7052_7])

theorem root_7053 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7053) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7053_0, decode 300 d_7053_1, decode 300 d_7053_2, decode 300 d_7053_3, decode 300 d_7053_4, decode 300 d_7053_5, decode 300 d_7053_6, decode 141 d_7053_7] (fun x hx => bits_full_and hx) cov_7053 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7053_0, ch_7053_1, ch_7053_2, ch_7053_3, ch_7053_4, ch_7053_5, ch_7053_6, ch_7053_7])

theorem root_7058 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7058) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7058_0, decode 300 d_7058_1, decode 300 d_7058_2, decode 300 d_7058_3, decode 300 d_7058_4, decode 300 d_7058_5, decode 300 d_7058_6, decode 142 d_7058_7] (fun x hx => bits_full_and hx) cov_7058 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7058_0, ch_7058_1, ch_7058_2, ch_7058_3, ch_7058_4, ch_7058_5, ch_7058_6, ch_7058_7])

theorem roots_105_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_105, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_105, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7011 hB hC hCl hCB, root_7012 hB hC hCl hCB, root_7014 hB hC hCl hCB, root_7015 hB hC hCl hCB, root_7020 hB hC hCl hCB, root_7021 hB hC hCl hCB, root_7022 hB hC hCl hCB, root_7029 hB hC hCl hCB, root_7030 hB hC hCl hCB, root_7031 hB hC hCl hCB, root_7033 hB hC hCl hCB, root_7037 hB hC hCl hCB, root_7045 hB hC hCl hCB, root_7046 hB hC hCl hCB, root_7047 hB hC hCl hCB, root_7052 hB hC hCl hCB, root_7053 hB hC hCl hCB, root_7058 hB hC hCl hCB]

theorem root_7059 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7059) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7059_0, decode 300 d_7059_1, decode 300 d_7059_2, decode 300 d_7059_3, decode 300 d_7059_4, decode 300 d_7059_5, decode 300 d_7059_6, decode 141 d_7059_7] (fun x hx => bits_full_and hx) cov_7059 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7059_0, ch_7059_1, ch_7059_2, ch_7059_3, ch_7059_4, ch_7059_5, ch_7059_6, ch_7059_7])

theorem root_7070 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7070) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7070_0, decode 300 d_7070_1, decode 300 d_7070_2, decode 300 d_7070_3, decode 300 d_7070_4, decode 300 d_7070_5, decode 300 d_7070_6, decode 141 d_7070_7] (fun x hx => bits_full_and hx) cov_7070 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7070_0, ch_7070_1, ch_7070_2, ch_7070_3, ch_7070_4, ch_7070_5, ch_7070_6, ch_7070_7])

theorem root_7078 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7078) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7078_0, decode 300 d_7078_1, decode 300 d_7078_2, decode 300 d_7078_3, decode 300 d_7078_4, decode 300 d_7078_5, decode 300 d_7078_6, decode 141 d_7078_7] (fun x hx => bits_full_and hx) cov_7078 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7078_0, ch_7078_1, ch_7078_2, ch_7078_3, ch_7078_4, ch_7078_5, ch_7078_6, ch_7078_7])

theorem root_7079 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7079) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7079_0, decode 300 d_7079_1, decode 300 d_7079_2, decode 300 d_7079_3, decode 300 d_7079_4, decode 300 d_7079_5, decode 300 d_7079_6, decode 141 d_7079_7] (fun x hx => bits_full_and hx) cov_7079 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7079_0, ch_7079_1, ch_7079_2, ch_7079_3, ch_7079_4, ch_7079_5, ch_7079_6, ch_7079_7])

theorem root_7087 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7087) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7087_0, decode 300 d_7087_1, decode 300 d_7087_2, decode 300 d_7087_3, decode 300 d_7087_4, decode 300 d_7087_5, decode 300 d_7087_6, decode 142 d_7087_7] (fun x hx => bits_full_and hx) cov_7087 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7087_0, ch_7087_1, ch_7087_2, ch_7087_3, ch_7087_4, ch_7087_5, ch_7087_6, ch_7087_7])

theorem root_7088 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7088) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7088_0, decode 300 d_7088_1, decode 300 d_7088_2, decode 300 d_7088_3, decode 300 d_7088_4, decode 300 d_7088_5, decode 300 d_7088_6, decode 142 d_7088_7] (fun x hx => bits_full_and hx) cov_7088 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7088_0, ch_7088_1, ch_7088_2, ch_7088_3, ch_7088_4, ch_7088_5, ch_7088_6, ch_7088_7])

theorem root_7089 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7089) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7089_0, decode 300 d_7089_1, decode 300 d_7089_2, decode 300 d_7089_3, decode 300 d_7089_4, decode 300 d_7089_5, decode 300 d_7089_6, decode 141 d_7089_7] (fun x hx => bits_full_and hx) cov_7089 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7089_0, ch_7089_1, ch_7089_2, ch_7089_3, ch_7089_4, ch_7089_5, ch_7089_6, ch_7089_7])

theorem root_7096 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7096) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7096_0, decode 300 d_7096_1, decode 300 d_7096_2, decode 300 d_7096_3, decode 300 d_7096_4, decode 300 d_7096_5, decode 300 d_7096_6, decode 142 d_7096_7] (fun x hx => bits_full_and hx) cov_7096 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7096_0, ch_7096_1, ch_7096_2, ch_7096_3, ch_7096_4, ch_7096_5, ch_7096_6, ch_7096_7])

theorem root_7098 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7098) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7098_0, decode 300 d_7098_1, decode 300 d_7098_2, decode 300 d_7098_3, decode 300 d_7098_4, decode 300 d_7098_5, decode 300 d_7098_6, decode 141 d_7098_7] (fun x hx => bits_full_and hx) cov_7098 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7098_0, ch_7098_1, ch_7098_2, ch_7098_3, ch_7098_4, ch_7098_5, ch_7098_6, ch_7098_7])

theorem root_7103 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7103) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7103_0, decode 300 d_7103_1, decode 300 d_7103_2, decode 300 d_7103_3, decode 300 d_7103_4, decode 300 d_7103_5, decode 300 d_7103_6, decode 142 d_7103_7] (fun x hx => bits_full_and hx) cov_7103 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7103_0, ch_7103_1, ch_7103_2, ch_7103_3, ch_7103_4, ch_7103_5, ch_7103_6, ch_7103_7])

theorem root_7104 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7104) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7104_0, decode 300 d_7104_1, decode 300 d_7104_2, decode 300 d_7104_3, decode 300 d_7104_4, decode 300 d_7104_5, decode 300 d_7104_6, decode 142 d_7104_7] (fun x hx => bits_full_and hx) cov_7104 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7104_0, ch_7104_1, ch_7104_2, ch_7104_3, ch_7104_4, ch_7104_5, ch_7104_6, ch_7104_7])

theorem root_7108 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7108) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7108_0, decode 300 d_7108_1, decode 300 d_7108_2, decode 300 d_7108_3, decode 300 d_7108_4, decode 300 d_7108_5, decode 300 d_7108_6, decode 142 d_7108_7] (fun x hx => bits_full_and hx) cov_7108 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7108_0, ch_7108_1, ch_7108_2, ch_7108_3, ch_7108_4, ch_7108_5, ch_7108_6, ch_7108_7])

theorem root_7109 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7109) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7109_0, decode 300 d_7109_1, decode 300 d_7109_2, decode 300 d_7109_3, decode 300 d_7109_4, decode 300 d_7109_5, decode 300 d_7109_6, decode 142 d_7109_7] (fun x hx => bits_full_and hx) cov_7109 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7109_0, ch_7109_1, ch_7109_2, ch_7109_3, ch_7109_4, ch_7109_5, ch_7109_6, ch_7109_7])

theorem root_7110 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7110) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7110_0, decode 300 d_7110_1, decode 300 d_7110_2, decode 300 d_7110_3, decode 300 d_7110_4, decode 300 d_7110_5, decode 300 d_7110_6, decode 141 d_7110_7] (fun x hx => bits_full_and hx) cov_7110 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7110_0, ch_7110_1, ch_7110_2, ch_7110_3, ch_7110_4, ch_7110_5, ch_7110_6, ch_7110_7])

theorem root_7112 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7112) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7112_0, decode 300 d_7112_1, decode 300 d_7112_2, decode 300 d_7112_3, decode 300 d_7112_4, decode 300 d_7112_5, decode 300 d_7112_6, decode 141 d_7112_7] (fun x hx => bits_full_and hx) cov_7112 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7112_0, ch_7112_1, ch_7112_2, ch_7112_3, ch_7112_4, ch_7112_5, ch_7112_6, ch_7112_7])

theorem root_7118 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7118) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7118_0, decode 300 d_7118_1, decode 300 d_7118_2, decode 300 d_7118_3, decode 300 d_7118_4, decode 300 d_7118_5, decode 300 d_7118_6, decode 141 d_7118_7] (fun x hx => bits_full_and hx) cov_7118 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7118_0, ch_7118_1, ch_7118_2, ch_7118_3, ch_7118_4, ch_7118_5, ch_7118_6, ch_7118_7])

theorem root_7125 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7125) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7125_0, decode 300 d_7125_1, decode 300 d_7125_2, decode 300 d_7125_3, decode 300 d_7125_4, decode 300 d_7125_5, decode 300 d_7125_6, decode 141 d_7125_7] (fun x hx => bits_full_and hx) cov_7125 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7125_0, ch_7125_1, ch_7125_2, ch_7125_3, ch_7125_4, ch_7125_5, ch_7125_6, ch_7125_7])

theorem root_7126 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7126) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7126_0, decode 300 d_7126_1, decode 300 d_7126_2, decode 300 d_7126_3, decode 300 d_7126_4, decode 300 d_7126_5, decode 300 d_7126_6, decode 141 d_7126_7] (fun x hx => bits_full_and hx) cov_7126 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7126_0, ch_7126_1, ch_7126_2, ch_7126_3, ch_7126_4, ch_7126_5, ch_7126_6, ch_7126_7])

theorem roots_106_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_106, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_106, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7059 hB hC hCl hCB, root_7070 hB hC hCl hCB, root_7078 hB hC hCl hCB, root_7079 hB hC hCl hCB, root_7087 hB hC hCl hCB, root_7088 hB hC hCl hCB, root_7089 hB hC hCl hCB, root_7096 hB hC hCl hCB, root_7098 hB hC hCl hCB, root_7103 hB hC hCl hCB, root_7104 hB hC hCl hCB, root_7108 hB hC hCl hCB, root_7109 hB hC hCl hCB, root_7110 hB hC hCl hCB, root_7112 hB hC hCl hCB, root_7118 hB hC hCl hCB, root_7125 hB hC hCl hCB, root_7126 hB hC hCl hCB]

theorem root_7140 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7140) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7140_0, decode 300 d_7140_1, decode 300 d_7140_2, decode 300 d_7140_3, decode 300 d_7140_4, decode 300 d_7140_5, decode 300 d_7140_6, decode 158 d_7140_7] (fun x hx => bits_full_and hx) cov_7140 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7140_0, ch_7140_1, ch_7140_2, ch_7140_3, ch_7140_4, ch_7140_5, ch_7140_6, ch_7140_7])

theorem root_7141 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7141) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7141_0, decode 300 d_7141_1, decode 300 d_7141_2, decode 300 d_7141_3, decode 300 d_7141_4, decode 300 d_7141_5, decode 300 d_7141_6, decode 141 d_7141_7] (fun x hx => bits_full_and hx) cov_7141 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7141_0, ch_7141_1, ch_7141_2, ch_7141_3, ch_7141_4, ch_7141_5, ch_7141_6, ch_7141_7])

theorem root_7142 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7142) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7142_0, decode 300 d_7142_1, decode 300 d_7142_2, decode 300 d_7142_3, decode 300 d_7142_4, decode 300 d_7142_5, decode 300 d_7142_6, decode 141 d_7142_7] (fun x hx => bits_full_and hx) cov_7142 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7142_0, ch_7142_1, ch_7142_2, ch_7142_3, ch_7142_4, ch_7142_5, ch_7142_6, ch_7142_7])

theorem root_7147 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7147) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7147_0, decode 300 d_7147_1, decode 300 d_7147_2, decode 300 d_7147_3, decode 300 d_7147_4, decode 300 d_7147_5, decode 300 d_7147_6, decode 141 d_7147_7] (fun x hx => bits_full_and hx) cov_7147 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7147_0, ch_7147_1, ch_7147_2, ch_7147_3, ch_7147_4, ch_7147_5, ch_7147_6, ch_7147_7])

theorem root_7152 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7152) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7152_0, decode 300 d_7152_1, decode 300 d_7152_2, decode 300 d_7152_3, decode 300 d_7152_4, decode 300 d_7152_5, decode 300 d_7152_6, decode 158 d_7152_7] (fun x hx => bits_full_and hx) cov_7152 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7152_0, ch_7152_1, ch_7152_2, ch_7152_3, ch_7152_4, ch_7152_5, ch_7152_6, ch_7152_7])

theorem root_7153 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7153) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7153_0, decode 300 d_7153_1, decode 300 d_7153_2, decode 300 d_7153_3, decode 300 d_7153_4, decode 300 d_7153_5, decode 300 d_7153_6, decode 158 d_7153_7] (fun x hx => bits_full_and hx) cov_7153 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7153_0, ch_7153_1, ch_7153_2, ch_7153_3, ch_7153_4, ch_7153_5, ch_7153_6, ch_7153_7])

theorem root_7155 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7155) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7155_0, decode 300 d_7155_1, decode 300 d_7155_2, decode 300 d_7155_3, decode 300 d_7155_4, decode 300 d_7155_5, decode 300 d_7155_6, decode 141 d_7155_7] (fun x hx => bits_full_and hx) cov_7155 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7155_0, ch_7155_1, ch_7155_2, ch_7155_3, ch_7155_4, ch_7155_5, ch_7155_6, ch_7155_7])

theorem root_7160 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7160) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7160_0, decode 300 d_7160_1, decode 300 d_7160_2, decode 300 d_7160_3, decode 300 d_7160_4, decode 300 d_7160_5, decode 300 d_7160_6, decode 158 d_7160_7] (fun x hx => bits_full_and hx) cov_7160 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7160_0, ch_7160_1, ch_7160_2, ch_7160_3, ch_7160_4, ch_7160_5, ch_7160_6, ch_7160_7])

theorem root_7162 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7162) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7162_0, decode 300 d_7162_1, decode 300 d_7162_2, decode 300 d_7162_3, decode 300 d_7162_4, decode 300 d_7162_5, decode 300 d_7162_6, decode 141 d_7162_7] (fun x hx => bits_full_and hx) cov_7162 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7162_0, ch_7162_1, ch_7162_2, ch_7162_3, ch_7162_4, ch_7162_5, ch_7162_6, ch_7162_7])

theorem root_7163 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7163) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7163_0, decode 300 d_7163_1, decode 300 d_7163_2, decode 300 d_7163_3, decode 300 d_7163_4, decode 300 d_7163_5, decode 300 d_7163_6, decode 141 d_7163_7] (fun x hx => bits_full_and hx) cov_7163 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7163_0, ch_7163_1, ch_7163_2, ch_7163_3, ch_7163_4, ch_7163_5, ch_7163_6, ch_7163_7])

theorem root_7165 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7165) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7165_0, decode 300 d_7165_1, decode 300 d_7165_2, decode 300 d_7165_3, decode 300 d_7165_4, decode 300 d_7165_5, decode 300 d_7165_6, decode 142 d_7165_7] (fun x hx => bits_full_and hx) cov_7165 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7165_0, ch_7165_1, ch_7165_2, ch_7165_3, ch_7165_4, ch_7165_5, ch_7165_6, ch_7165_7])

theorem root_7166 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7166) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7166_0, decode 300 d_7166_1, decode 300 d_7166_2, decode 300 d_7166_3, decode 300 d_7166_4, decode 300 d_7166_5, decode 300 d_7166_6, decode 142 d_7166_7] (fun x hx => bits_full_and hx) cov_7166 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7166_0, ch_7166_1, ch_7166_2, ch_7166_3, ch_7166_4, ch_7166_5, ch_7166_6, ch_7166_7])

theorem root_7167 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7167) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7167_0, decode 300 d_7167_1, decode 300 d_7167_2, decode 300 d_7167_3, decode 300 d_7167_4, decode 300 d_7167_5, decode 300 d_7167_6, decode 141 d_7167_7] (fun x hx => bits_full_and hx) cov_7167 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7167_0, ch_7167_1, ch_7167_2, ch_7167_3, ch_7167_4, ch_7167_5, ch_7167_6, ch_7167_7])

theorem root_7168 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7168) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7168_0, decode 300 d_7168_1, decode 300 d_7168_2, decode 300 d_7168_3, decode 300 d_7168_4, decode 300 d_7168_5, decode 300 d_7168_6, decode 141 d_7168_7] (fun x hx => bits_full_and hx) cov_7168 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7168_0, ch_7168_1, ch_7168_2, ch_7168_3, ch_7168_4, ch_7168_5, ch_7168_6, ch_7168_7])

theorem root_7173 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7173) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7173_0, decode 300 d_7173_1, decode 300 d_7173_2, decode 300 d_7173_3, decode 300 d_7173_4, decode 300 d_7173_5, decode 300 d_7173_6, decode 142 d_7173_7] (fun x hx => bits_full_and hx) cov_7173 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7173_0, ch_7173_1, ch_7173_2, ch_7173_3, ch_7173_4, ch_7173_5, ch_7173_6, ch_7173_7])

theorem root_7175 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7175) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7175_0, decode 300 d_7175_1, decode 300 d_7175_2, decode 300 d_7175_3, decode 300 d_7175_4, decode 300 d_7175_5, decode 300 d_7175_6, decode 141 d_7175_7] (fun x hx => bits_full_and hx) cov_7175 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7175_0, ch_7175_1, ch_7175_2, ch_7175_3, ch_7175_4, ch_7175_5, ch_7175_6, ch_7175_7])

theorem root_7181 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7181) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7181_0, decode 300 d_7181_1, decode 300 d_7181_2, decode 300 d_7181_3, decode 300 d_7181_4, decode 300 d_7181_5, decode 300 d_7181_6, decode 141 d_7181_7] (fun x hx => bits_full_and hx) cov_7181 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7181_0, ch_7181_1, ch_7181_2, ch_7181_3, ch_7181_4, ch_7181_5, ch_7181_6, ch_7181_7])

theorem root_7187 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7187) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7187_0, decode 300 d_7187_1, decode 300 d_7187_2, decode 300 d_7187_3, decode 300 d_7187_4, decode 300 d_7187_5, decode 300 d_7187_6, decode 142 d_7187_7] (fun x hx => bits_full_and hx) cov_7187 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7187_0, ch_7187_1, ch_7187_2, ch_7187_3, ch_7187_4, ch_7187_5, ch_7187_6, ch_7187_7])

theorem roots_107_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_107, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_107, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7140 hB hC hCl hCB, root_7141 hB hC hCl hCB, root_7142 hB hC hCl hCB, root_7147 hB hC hCl hCB, root_7152 hB hC hCl hCB, root_7153 hB hC hCl hCB, root_7155 hB hC hCl hCB, root_7160 hB hC hCl hCB, root_7162 hB hC hCl hCB, root_7163 hB hC hCl hCB, root_7165 hB hC hCl hCB, root_7166 hB hC hCl hCB, root_7167 hB hC hCl hCB, root_7168 hB hC hCl hCB, root_7173 hB hC hCl hCB, root_7175 hB hC hCl hCB, root_7181 hB hC hCl hCB, root_7187 hB hC hCl hCB]

theorem root_7199 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7199) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7199_0, decode 300 d_7199_1, decode 300 d_7199_2, decode 300 d_7199_3, decode 300 d_7199_4, decode 300 d_7199_5, decode 300 d_7199_6, decode 141 d_7199_7] (fun x hx => bits_full_and hx) cov_7199 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7199_0, ch_7199_1, ch_7199_2, ch_7199_3, ch_7199_4, ch_7199_5, ch_7199_6, ch_7199_7])

theorem root_7203 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7203) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7203_0, decode 300 d_7203_1, decode 300 d_7203_2, decode 300 d_7203_3, decode 300 d_7203_4, decode 300 d_7203_5, decode 300 d_7203_6, decode 141 d_7203_7] (fun x hx => bits_full_and hx) cov_7203 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7203_0, ch_7203_1, ch_7203_2, ch_7203_3, ch_7203_4, ch_7203_5, ch_7203_6, ch_7203_7])

theorem root_7205 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7205) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7205_0, decode 300 d_7205_1, decode 300 d_7205_2, decode 300 d_7205_3, decode 300 d_7205_4, decode 300 d_7205_5, decode 300 d_7205_6, decode 141 d_7205_7] (fun x hx => bits_full_and hx) cov_7205 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7205_0, ch_7205_1, ch_7205_2, ch_7205_3, ch_7205_4, ch_7205_5, ch_7205_6, ch_7205_7])

theorem root_7206 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7206) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7206_0, decode 300 d_7206_1, decode 300 d_7206_2, decode 300 d_7206_3, decode 300 d_7206_4, decode 300 d_7206_5, decode 300 d_7206_6, decode 141 d_7206_7] (fun x hx => bits_full_and hx) cov_7206 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7206_0, ch_7206_1, ch_7206_2, ch_7206_3, ch_7206_4, ch_7206_5, ch_7206_6, ch_7206_7])

theorem root_7207 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7207) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7207_0, decode 300 d_7207_1, decode 300 d_7207_2, decode 300 d_7207_3, decode 300 d_7207_4, decode 300 d_7207_5, decode 300 d_7207_6, decode 141 d_7207_7] (fun x hx => bits_full_and hx) cov_7207 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7207_0, ch_7207_1, ch_7207_2, ch_7207_3, ch_7207_4, ch_7207_5, ch_7207_6, ch_7207_7])

theorem root_7210 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7210) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7210_0, decode 300 d_7210_1, decode 300 d_7210_2, decode 300 d_7210_3, decode 300 d_7210_4, decode 300 d_7210_5, decode 300 d_7210_6, decode 141 d_7210_7] (fun x hx => bits_full_and hx) cov_7210 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7210_0, ch_7210_1, ch_7210_2, ch_7210_3, ch_7210_4, ch_7210_5, ch_7210_6, ch_7210_7])

theorem root_7213 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7213) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7213_0, decode 300 d_7213_1, decode 300 d_7213_2, decode 300 d_7213_3, decode 300 d_7213_4, decode 300 d_7213_5, decode 300 d_7213_6, decode 141 d_7213_7] (fun x hx => bits_full_and hx) cov_7213 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7213_0, ch_7213_1, ch_7213_2, ch_7213_3, ch_7213_4, ch_7213_5, ch_7213_6, ch_7213_7])

theorem root_7219 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7219) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7219_0, decode 300 d_7219_1, decode 300 d_7219_2, decode 300 d_7219_3, decode 300 d_7219_4, decode 300 d_7219_5, decode 300 d_7219_6, decode 141 d_7219_7] (fun x hx => bits_full_and hx) cov_7219 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7219_0, ch_7219_1, ch_7219_2, ch_7219_3, ch_7219_4, ch_7219_5, ch_7219_6, ch_7219_7])

theorem root_7220 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7220) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7220_0, decode 300 d_7220_1, decode 300 d_7220_2, decode 300 d_7220_3, decode 300 d_7220_4, decode 300 d_7220_5, decode 300 d_7220_6, decode 141 d_7220_7] (fun x hx => bits_full_and hx) cov_7220 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7220_0, ch_7220_1, ch_7220_2, ch_7220_3, ch_7220_4, ch_7220_5, ch_7220_6, ch_7220_7])

theorem root_7221 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7221) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7221_0, decode 300 d_7221_1, decode 300 d_7221_2, decode 300 d_7221_3, decode 300 d_7221_4, decode 300 d_7221_5, decode 300 d_7221_6, decode 141 d_7221_7] (fun x hx => bits_full_and hx) cov_7221 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7221_0, ch_7221_1, ch_7221_2, ch_7221_3, ch_7221_4, ch_7221_5, ch_7221_6, ch_7221_7])

theorem root_7231 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7231) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7231_0, decode 300 d_7231_1, decode 300 d_7231_2, decode 300 d_7231_3, decode 300 d_7231_4, decode 300 d_7231_5, decode 300 d_7231_6, decode 141 d_7231_7] (fun x hx => bits_full_and hx) cov_7231 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7231_0, ch_7231_1, ch_7231_2, ch_7231_3, ch_7231_4, ch_7231_5, ch_7231_6, ch_7231_7])

theorem root_7240 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7240) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7240_0, decode 300 d_7240_1, decode 300 d_7240_2, decode 300 d_7240_3, decode 300 d_7240_4, decode 300 d_7240_5, decode 300 d_7240_6, decode 141 d_7240_7] (fun x hx => bits_full_and hx) cov_7240 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7240_0, ch_7240_1, ch_7240_2, ch_7240_3, ch_7240_4, ch_7240_5, ch_7240_6, ch_7240_7])

theorem root_7241 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7241) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7241_0, decode 300 d_7241_1, decode 300 d_7241_2, decode 300 d_7241_3, decode 300 d_7241_4, decode 300 d_7241_5, decode 300 d_7241_6, decode 141 d_7241_7] (fun x hx => bits_full_and hx) cov_7241 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7241_0, ch_7241_1, ch_7241_2, ch_7241_3, ch_7241_4, ch_7241_5, ch_7241_6, ch_7241_7])

theorem root_7261 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7261) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7261_0, decode 300 d_7261_1, decode 300 d_7261_2, decode 300 d_7261_3, decode 300 d_7261_4, decode 273 d_7261_5] (fun x hx => bits_full_and hx) cov_7261 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7261_0, ch_7261_1, ch_7261_2, ch_7261_3, ch_7261_4, ch_7261_5])

theorem root_7262 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7262) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7262_0, decode 300 d_7262_1, decode 300 d_7262_2, decode 300 d_7262_3, decode 300 d_7262_4, decode 300 d_7262_5, decode 15 d_7262_6] (fun x hx => bits_full_and hx) cov_7262 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7262_0, ch_7262_1, ch_7262_2, ch_7262_3, ch_7262_4, ch_7262_5, ch_7262_6])

theorem root_7263 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7263) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7263_0, decode 300 d_7263_1, decode 300 d_7263_2, decode 300 d_7263_3, decode 300 d_7263_4, decode 300 d_7263_5, decode 15 d_7263_6] (fun x hx => bits_full_and hx) cov_7263 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7263_0, ch_7263_1, ch_7263_2, ch_7263_3, ch_7263_4, ch_7263_5, ch_7263_6])

theorem root_7264 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7264) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7264_0, decode 300 d_7264_1, decode 300 d_7264_2, decode 300 d_7264_3, decode 300 d_7264_4, decode 300 d_7264_5, decode 15 d_7264_6] (fun x hx => bits_full_and hx) cov_7264 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7264_0, ch_7264_1, ch_7264_2, ch_7264_3, ch_7264_4, ch_7264_5, ch_7264_6])

theorem root_7270 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7270) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7270_0, decode 300 d_7270_1, decode 300 d_7270_2, decode 300 d_7270_3, decode 300 d_7270_4, decode 273 d_7270_5] (fun x hx => bits_full_and hx) cov_7270 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7270_0, ch_7270_1, ch_7270_2, ch_7270_3, ch_7270_4, ch_7270_5])

theorem root_7273 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7273) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7273_0, decode 300 d_7273_1, decode 300 d_7273_2, decode 300 d_7273_3, decode 300 d_7273_4, decode 300 d_7273_5, decode 300 d_7273_6, decode 141 d_7273_7] (fun x hx => bits_full_and hx) cov_7273 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7273_0, ch_7273_1, ch_7273_2, ch_7273_3, ch_7273_4, ch_7273_5, ch_7273_6, ch_7273_7])

theorem roots_108_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_108, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_108, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7199 hB hC hCl hCB, root_7203 hB hC hCl hCB, root_7205 hB hC hCl hCB, root_7206 hB hC hCl hCB, root_7207 hB hC hCl hCB, root_7210 hB hC hCl hCB, root_7213 hB hC hCl hCB, root_7219 hB hC hCl hCB, root_7220 hB hC hCl hCB, root_7221 hB hC hCl hCB, root_7231 hB hC hCl hCB, root_7240 hB hC hCl hCB, root_7241 hB hC hCl hCB, root_7261 hB hC hCl hCB, root_7262 hB hC hCl hCB, root_7263 hB hC hCl hCB, root_7264 hB hC hCl hCB, root_7270 hB hC hCl hCB, root_7273 hB hC hCl hCB]

theorem root_7274 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7274) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7274_0, decode 300 d_7274_1, decode 300 d_7274_2, decode 300 d_7274_3, decode 300 d_7274_4, decode 300 d_7274_5, decode 300 d_7274_6, decode 141 d_7274_7] (fun x hx => bits_full_and hx) cov_7274 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7274_0, ch_7274_1, ch_7274_2, ch_7274_3, ch_7274_4, ch_7274_5, ch_7274_6, ch_7274_7])

theorem root_7275 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7275) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7275_0, decode 300 d_7275_1, decode 300 d_7275_2, decode 300 d_7275_3, decode 300 d_7275_4, decode 300 d_7275_5, decode 300 d_7275_6, decode 161 d_7275_7] (fun x hx => bits_full_and hx) cov_7275 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7275_0, ch_7275_1, ch_7275_2, ch_7275_3, ch_7275_4, ch_7275_5, ch_7275_6, ch_7275_7])

theorem root_7276 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7276) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7276_0, decode 300 d_7276_1, decode 300 d_7276_2, decode 300 d_7276_3, decode 300 d_7276_4, decode 300 d_7276_5, decode 300 d_7276_6, decode 161 d_7276_7] (fun x hx => bits_full_and hx) cov_7276 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7276_0, ch_7276_1, ch_7276_2, ch_7276_3, ch_7276_4, ch_7276_5, ch_7276_6, ch_7276_7])

theorem root_7287 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7287) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7287_0, decode 300 d_7287_1, decode 300 d_7287_2, decode 300 d_7287_3, decode 300 d_7287_4, decode 300 d_7287_5, decode 300 d_7287_6, decode 158 d_7287_7] (fun x hx => bits_full_and hx) cov_7287 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7287_0, ch_7287_1, ch_7287_2, ch_7287_3, ch_7287_4, ch_7287_5, ch_7287_6, ch_7287_7])

theorem root_7288 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7288) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7288_0, decode 300 d_7288_1, decode 300 d_7288_2, decode 300 d_7288_3, decode 300 d_7288_4, decode 300 d_7288_5, decode 300 d_7288_6, decode 141 d_7288_7] (fun x hx => bits_full_and hx) cov_7288 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7288_0, ch_7288_1, ch_7288_2, ch_7288_3, ch_7288_4, ch_7288_5, ch_7288_6, ch_7288_7])

theorem root_7289 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7289) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7289_0, decode 300 d_7289_1, decode 300 d_7289_2, decode 300 d_7289_3, decode 300 d_7289_4, decode 300 d_7289_5, decode 300 d_7289_6, decode 141 d_7289_7] (fun x hx => bits_full_and hx) cov_7289 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7289_0, ch_7289_1, ch_7289_2, ch_7289_3, ch_7289_4, ch_7289_5, ch_7289_6, ch_7289_7])

theorem root_7290 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7290) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7290_0, decode 300 d_7290_1, decode 300 d_7290_2, decode 300 d_7290_3, decode 300 d_7290_4, decode 300 d_7290_5, decode 300 d_7290_6, decode 141 d_7290_7] (fun x hx => bits_full_and hx) cov_7290 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7290_0, ch_7290_1, ch_7290_2, ch_7290_3, ch_7290_4, ch_7290_5, ch_7290_6, ch_7290_7])

theorem root_7301 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7301) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7301_0, decode 300 d_7301_1, decode 300 d_7301_2, decode 300 d_7301_3, decode 300 d_7301_4, decode 300 d_7301_5, decode 300 d_7301_6, decode 158 d_7301_7] (fun x hx => bits_full_and hx) cov_7301 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7301_0, ch_7301_1, ch_7301_2, ch_7301_3, ch_7301_4, ch_7301_5, ch_7301_6, ch_7301_7])

theorem root_7302 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7302) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7302_0, decode 300 d_7302_1, decode 300 d_7302_2, decode 300 d_7302_3, decode 300 d_7302_4, decode 300 d_7302_5, decode 300 d_7302_6, decode 158 d_7302_7] (fun x hx => bits_full_and hx) cov_7302 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7302_0, ch_7302_1, ch_7302_2, ch_7302_3, ch_7302_4, ch_7302_5, ch_7302_6, ch_7302_7])

theorem root_7303 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7303) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7303_0, decode 300 d_7303_1, decode 300 d_7303_2, decode 300 d_7303_3, decode 300 d_7303_4, decode 300 d_7303_5, decode 300 d_7303_6, decode 158 d_7303_7] (fun x hx => bits_full_and hx) cov_7303 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7303_0, ch_7303_1, ch_7303_2, ch_7303_3, ch_7303_4, ch_7303_5, ch_7303_6, ch_7303_7])

theorem root_7305 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7305) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7305_0, decode 300 d_7305_1, decode 300 d_7305_2, decode 300 d_7305_3, decode 300 d_7305_4, decode 300 d_7305_5, decode 300 d_7305_6, decode 141 d_7305_7] (fun x hx => bits_full_and hx) cov_7305 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7305_0, ch_7305_1, ch_7305_2, ch_7305_3, ch_7305_4, ch_7305_5, ch_7305_6, ch_7305_7])

theorem root_7306 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7306) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7306_0, decode 300 d_7306_1, decode 300 d_7306_2, decode 300 d_7306_3, decode 300 d_7306_4, decode 300 d_7306_5, decode 300 d_7306_6, decode 141 d_7306_7] (fun x hx => bits_full_and hx) cov_7306 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7306_0, ch_7306_1, ch_7306_2, ch_7306_3, ch_7306_4, ch_7306_5, ch_7306_6, ch_7306_7])

theorem root_7313 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7313) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7313_0, decode 300 d_7313_1, decode 300 d_7313_2, decode 300 d_7313_3, decode 300 d_7313_4, decode 300 d_7313_5, decode 300 d_7313_6, decode 158 d_7313_7] (fun x hx => bits_full_and hx) cov_7313 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7313_0, ch_7313_1, ch_7313_2, ch_7313_3, ch_7313_4, ch_7313_5, ch_7313_6, ch_7313_7])

theorem root_7314 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7314) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7314_0, decode 300 d_7314_1, decode 300 d_7314_2, decode 300 d_7314_3, decode 300 d_7314_4, decode 300 d_7314_5, decode 300 d_7314_6, decode 141 d_7314_7] (fun x hx => bits_full_and hx) cov_7314 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7314_0, ch_7314_1, ch_7314_2, ch_7314_3, ch_7314_4, ch_7314_5, ch_7314_6, ch_7314_7])

theorem root_7321 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7321) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7321_0, decode 300 d_7321_1, decode 300 d_7321_2, decode 300 d_7321_3, decode 300 d_7321_4, decode 300 d_7321_5, decode 300 d_7321_6, decode 158 d_7321_7] (fun x hx => bits_full_and hx) cov_7321 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7321_0, ch_7321_1, ch_7321_2, ch_7321_3, ch_7321_4, ch_7321_5, ch_7321_6, ch_7321_7])

theorem root_7322 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7322) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7322_0, decode 300 d_7322_1, decode 300 d_7322_2, decode 300 d_7322_3, decode 300 d_7322_4, decode 300 d_7322_5, decode 300 d_7322_6, decode 141 d_7322_7] (fun x hx => bits_full_and hx) cov_7322 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7322_0, ch_7322_1, ch_7322_2, ch_7322_3, ch_7322_4, ch_7322_5, ch_7322_6, ch_7322_7])

theorem root_7323 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7323) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7323_0, decode 300 d_7323_1, decode 300 d_7323_2, decode 300 d_7323_3, decode 300 d_7323_4, decode 300 d_7323_5, decode 195 d_7323_6] (fun x hx => bits_full_and hx) cov_7323 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7323_0, ch_7323_1, ch_7323_2, ch_7323_3, ch_7323_4, ch_7323_5, ch_7323_6])

theorem root_7330 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7330) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7330_0, decode 300 d_7330_1, decode 300 d_7330_2, decode 300 d_7330_3, decode 300 d_7330_4, decode 273 d_7330_5] (fun x hx => bits_full_and hx) cov_7330 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7330_0, ch_7330_1, ch_7330_2, ch_7330_3, ch_7330_4, ch_7330_5])

theorem root_7331 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 7331) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_7331_0, decode 300 d_7331_1, decode 300 d_7331_2, decode 300 d_7331_3, decode 300 d_7331_4, decode 300 d_7331_5, decode 15 d_7331_6] (fun x hx => bits_full_and hx) cov_7331 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_7331_0, ch_7331_1, ch_7331_2, ch_7331_3, ch_7331_4, ch_7331_5, ch_7331_6])

theorem roots_109_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_109, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_109, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_7274 hB hC hCl hCB, root_7275 hB hC hCl hCB, root_7276 hB hC hCl hCB, root_7287 hB hC hCl hCB, root_7288 hB hC hCl hCB, root_7289 hB hC hCl hCB, root_7290 hB hC hCl hCB, root_7301 hB hC hCl hCB, root_7302 hB hC hCl hCB, root_7303 hB hC hCl hCB, root_7305 hB hC hCl hCB, root_7306 hB hC hCl hCB, root_7313 hB hC hCl hCB, root_7314 hB hC hCl hCB, root_7321 hB hC hCl hCB, root_7322 hB hC hCl hCB, root_7323 hB hC hCl hCB, root_7330 hB hC hCl hCB, root_7331 hB hC hCl hCB]

end LRC.O7U5
