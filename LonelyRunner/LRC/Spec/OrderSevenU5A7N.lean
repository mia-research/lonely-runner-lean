import LonelyRunner.LRC.Spec.OrderSevenU5SoundN
import LonelyRunner.LRC.Spec.OrderSevenU5C70N
import LonelyRunner.LRC.Spec.OrderSevenU5C71N
import LonelyRunner.LRC.Spec.OrderSevenU5C72N
import LonelyRunner.LRC.Spec.OrderSevenU5C73N
import LonelyRunner.LRC.Spec.OrderSevenU5C74N
import LonelyRunner.LRC.Spec.OrderSevenU5C75N
import LonelyRunner.LRC.Spec.OrderSevenU5C76N
import LonelyRunner.LRC.Spec.OrderSevenU5C77N
import LonelyRunner.LRC.Spec.OrderSevenU5C78N
import LonelyRunner.LRC.Spec.OrderSevenU5C79N

set_option maxRecDepth 100000

namespace LRC.O7U5

theorem root_4684 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4684) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4684_0, decode 300 d_4684_1, decode 300 d_4684_2, decode 300 d_4684_3, decode 300 d_4684_4, decode 300 d_4684_5, decode 93 d_4684_6] (fun x hx => bits_full_and hx) cov_4684 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4684_0, ch_4684_1, ch_4684_2, ch_4684_3, ch_4684_4, ch_4684_5, ch_4684_6])

theorem root_4686 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4686) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4686_0, decode 300 d_4686_1, decode 300 d_4686_2, decode 300 d_4686_3, decode 300 d_4686_4, decode 300 d_4686_5, decode 12 d_4686_6] (fun x hx => bits_full_and hx) cov_4686 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4686_0, ch_4686_1, ch_4686_2, ch_4686_3, ch_4686_4, ch_4686_5, ch_4686_6])

theorem root_4693 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4693) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4693_0, decode 300 d_4693_1, decode 300 d_4693_2, decode 300 d_4693_3, decode 300 d_4693_4, decode 300 d_4693_5, decode 76 d_4693_6] (fun x hx => bits_full_and hx) cov_4693 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4693_0, ch_4693_1, ch_4693_2, ch_4693_3, ch_4693_4, ch_4693_5, ch_4693_6])

theorem root_4695 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4695) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4695_0, decode 300 d_4695_1, decode 300 d_4695_2, decode 300 d_4695_3, decode 300 d_4695_4, decode 300 d_4695_5, decode 300 d_4695_6, decode 141 d_4695_7] (fun x hx => bits_full_and hx) cov_4695 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4695_0, ch_4695_1, ch_4695_2, ch_4695_3, ch_4695_4, ch_4695_5, ch_4695_6, ch_4695_7])

theorem root_4700 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4700) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4700_0, decode 300 d_4700_1, decode 300 d_4700_2, decode 300 d_4700_3, decode 300 d_4700_4, decode 300 d_4700_5, decode 76 d_4700_6] (fun x hx => bits_full_and hx) cov_4700 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4700_0, ch_4700_1, ch_4700_2, ch_4700_3, ch_4700_4, ch_4700_5, ch_4700_6])

theorem root_4703 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4703) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4703_0, decode 300 d_4703_1, decode 300 d_4703_2, decode 300 d_4703_3, decode 300 d_4703_4, decode 300 d_4703_5, decode 300 d_4703_6, decode 141 d_4703_7] (fun x hx => bits_full_and hx) cov_4703 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4703_0, ch_4703_1, ch_4703_2, ch_4703_3, ch_4703_4, ch_4703_5, ch_4703_6, ch_4703_7])

theorem root_4704 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4704) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4704_0, decode 300 d_4704_1, decode 300 d_4704_2, decode 300 d_4704_3, decode 300 d_4704_4, decode 300 d_4704_5, decode 300 d_4704_6, decode 141 d_4704_7] (fun x hx => bits_full_and hx) cov_4704 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4704_0, ch_4704_1, ch_4704_2, ch_4704_3, ch_4704_4, ch_4704_5, ch_4704_6, ch_4704_7])

theorem root_4708 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4708) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4708_0, decode 300 d_4708_1, decode 300 d_4708_2, decode 300 d_4708_3, decode 300 d_4708_4, decode 300 d_4708_5, decode 19 d_4708_6] (fun x hx => bits_full_and hx) cov_4708 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4708_0, ch_4708_1, ch_4708_2, ch_4708_3, ch_4708_4, ch_4708_5, ch_4708_6])

theorem root_4709 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4709) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4709_0, decode 300 d_4709_1, decode 300 d_4709_2, decode 300 d_4709_3, decode 300 d_4709_4, decode 300 d_4709_5, decode 19 d_4709_6] (fun x hx => bits_full_and hx) cov_4709 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4709_0, ch_4709_1, ch_4709_2, ch_4709_3, ch_4709_4, ch_4709_5, ch_4709_6])

theorem root_4715 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4715) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4715_0, decode 300 d_4715_1, decode 300 d_4715_2, decode 300 d_4715_3, decode 300 d_4715_4, decode 300 d_4715_5, decode 300 d_4715_6, decode 142 d_4715_7] (fun x hx => bits_full_and hx) cov_4715 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4715_0, ch_4715_1, ch_4715_2, ch_4715_3, ch_4715_4, ch_4715_5, ch_4715_6, ch_4715_7])

theorem root_4724 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4724) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4724_0, decode 300 d_4724_1, decode 300 d_4724_2, decode 300 d_4724_3, decode 300 d_4724_4, decode 300 d_4724_5, decode 300 d_4724_6, decode 141 d_4724_7] (fun x hx => bits_full_and hx) cov_4724 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4724_0, ch_4724_1, ch_4724_2, ch_4724_3, ch_4724_4, ch_4724_5, ch_4724_6, ch_4724_7])

theorem root_4725 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4725) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4725_0, decode 300 d_4725_1, decode 300 d_4725_2, decode 300 d_4725_3, decode 300 d_4725_4, decode 300 d_4725_5, decode 300 d_4725_6, decode 142 d_4725_7] (fun x hx => bits_full_and hx) cov_4725 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4725_0, ch_4725_1, ch_4725_2, ch_4725_3, ch_4725_4, ch_4725_5, ch_4725_6, ch_4725_7])

theorem root_4726 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4726) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4726_0, decode 300 d_4726_1, decode 300 d_4726_2, decode 300 d_4726_3, decode 300 d_4726_4, decode 300 d_4726_5, decode 300 d_4726_6, decode 142 d_4726_7] (fun x hx => bits_full_and hx) cov_4726 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4726_0, ch_4726_1, ch_4726_2, ch_4726_3, ch_4726_4, ch_4726_5, ch_4726_6, ch_4726_7])

theorem root_4729 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4729) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4729_0, decode 300 d_4729_1, decode 300 d_4729_2, decode 300 d_4729_3, decode 300 d_4729_4, decode 300 d_4729_5, decode 300 d_4729_6, decode 142 d_4729_7] (fun x hx => bits_full_and hx) cov_4729 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4729_0, ch_4729_1, ch_4729_2, ch_4729_3, ch_4729_4, ch_4729_5, ch_4729_6, ch_4729_7])

theorem root_4730 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4730) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4730_0, decode 300 d_4730_1, decode 300 d_4730_2, decode 300 d_4730_3, decode 300 d_4730_4, decode 300 d_4730_5, decode 300 d_4730_6, decode 142 d_4730_7] (fun x hx => bits_full_and hx) cov_4730 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4730_0, ch_4730_1, ch_4730_2, ch_4730_3, ch_4730_4, ch_4730_5, ch_4730_6, ch_4730_7])

theorem root_4731 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4731) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4731_0, decode 300 d_4731_1, decode 300 d_4731_2, decode 300 d_4731_3, decode 300 d_4731_4, decode 300 d_4731_5, decode 300 d_4731_6, decode 142 d_4731_7] (fun x hx => bits_full_and hx) cov_4731 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4731_0, ch_4731_1, ch_4731_2, ch_4731_3, ch_4731_4, ch_4731_5, ch_4731_6, ch_4731_7])

theorem root_4740 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4740) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4740_0, decode 300 d_4740_1, decode 300 d_4740_2, decode 300 d_4740_3, decode 300 d_4740_4, decode 300 d_4740_5, decode 300 d_4740_6, decode 142 d_4740_7] (fun x hx => bits_full_and hx) cov_4740 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4740_0, ch_4740_1, ch_4740_2, ch_4740_3, ch_4740_4, ch_4740_5, ch_4740_6, ch_4740_7])

theorem root_4747 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4747) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4747_0, decode 300 d_4747_1, decode 300 d_4747_2, decode 300 d_4747_3, decode 300 d_4747_4, decode 300 d_4747_5, decode 300 d_4747_6, decode 142 d_4747_7] (fun x hx => bits_full_and hx) cov_4747 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4747_0, ch_4747_1, ch_4747_2, ch_4747_3, ch_4747_4, ch_4747_5, ch_4747_6, ch_4747_7])

theorem root_4748 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4748) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4748_0, decode 300 d_4748_1, decode 300 d_4748_2, decode 300 d_4748_3, decode 300 d_4748_4, decode 300 d_4748_5, decode 300 d_4748_6, decode 142 d_4748_7] (fun x hx => bits_full_and hx) cov_4748 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4748_0, ch_4748_1, ch_4748_2, ch_4748_3, ch_4748_4, ch_4748_5, ch_4748_6, ch_4748_7])

theorem roots_70_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_70, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_70, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_4684 hB hC hCl hCB, root_4686 hB hC hCl hCB, root_4693 hB hC hCl hCB, root_4695 hB hC hCl hCB, root_4700 hB hC hCl hCB, root_4703 hB hC hCl hCB, root_4704 hB hC hCl hCB, root_4708 hB hC hCl hCB, root_4709 hB hC hCl hCB, root_4715 hB hC hCl hCB, root_4724 hB hC hCl hCB, root_4725 hB hC hCl hCB, root_4726 hB hC hCl hCB, root_4729 hB hC hCl hCB, root_4730 hB hC hCl hCB, root_4731 hB hC hCl hCB, root_4740 hB hC hCl hCB, root_4747 hB hC hCl hCB, root_4748 hB hC hCl hCB]

theorem root_4749 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4749) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4749_0, decode 300 d_4749_1, decode 300 d_4749_2, decode 300 d_4749_3, decode 300 d_4749_4, decode 300 d_4749_5, decode 300 d_4749_6, decode 142 d_4749_7] (fun x hx => bits_full_and hx) cov_4749 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4749_0, ch_4749_1, ch_4749_2, ch_4749_3, ch_4749_4, ch_4749_5, ch_4749_6, ch_4749_7])

theorem root_4761 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4761) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4761_0, decode 300 d_4761_1, decode 300 d_4761_2, decode 300 d_4761_3, decode 300 d_4761_4, decode 300 d_4761_5, decode 300 d_4761_6, decode 142 d_4761_7] (fun x hx => bits_full_and hx) cov_4761 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4761_0, ch_4761_1, ch_4761_2, ch_4761_3, ch_4761_4, ch_4761_5, ch_4761_6, ch_4761_7])

theorem root_4762 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4762) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4762_0, decode 300 d_4762_1, decode 300 d_4762_2, decode 300 d_4762_3, decode 300 d_4762_4, decode 300 d_4762_5, decode 300 d_4762_6, decode 142 d_4762_7] (fun x hx => bits_full_and hx) cov_4762 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4762_0, ch_4762_1, ch_4762_2, ch_4762_3, ch_4762_4, ch_4762_5, ch_4762_6, ch_4762_7])

theorem root_4763 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4763) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4763_0, decode 300 d_4763_1, decode 300 d_4763_2, decode 300 d_4763_3, decode 300 d_4763_4, decode 300 d_4763_5, decode 300 d_4763_6, decode 141 d_4763_7] (fun x hx => bits_full_and hx) cov_4763 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4763_0, ch_4763_1, ch_4763_2, ch_4763_3, ch_4763_4, ch_4763_5, ch_4763_6, ch_4763_7])

theorem root_4764 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4764) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4764_0, decode 300 d_4764_1, decode 300 d_4764_2, decode 300 d_4764_3, decode 300 d_4764_4, decode 300 d_4764_5, decode 300 d_4764_6, decode 141 d_4764_7] (fun x hx => bits_full_and hx) cov_4764 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4764_0, ch_4764_1, ch_4764_2, ch_4764_3, ch_4764_4, ch_4764_5, ch_4764_6, ch_4764_7])

theorem root_4770 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4770) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4770_0, decode 300 d_4770_1, decode 300 d_4770_2, decode 300 d_4770_3, decode 300 d_4770_4, decode 300 d_4770_5, decode 300 d_4770_6, decode 142 d_4770_7] (fun x hx => bits_full_and hx) cov_4770 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4770_0, ch_4770_1, ch_4770_2, ch_4770_3, ch_4770_4, ch_4770_5, ch_4770_6, ch_4770_7])

theorem root_4771 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4771) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4771_0, decode 300 d_4771_1, decode 300 d_4771_2, decode 300 d_4771_3, decode 300 d_4771_4, decode 300 d_4771_5, decode 300 d_4771_6, decode 141 d_4771_7] (fun x hx => bits_full_and hx) cov_4771 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4771_0, ch_4771_1, ch_4771_2, ch_4771_3, ch_4771_4, ch_4771_5, ch_4771_6, ch_4771_7])

theorem root_4772 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4772) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4772_0, decode 300 d_4772_1, decode 300 d_4772_2, decode 300 d_4772_3, decode 300 d_4772_4, decode 300 d_4772_5, decode 300 d_4772_6, decode 141 d_4772_7] (fun x hx => bits_full_and hx) cov_4772 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4772_0, ch_4772_1, ch_4772_2, ch_4772_3, ch_4772_4, ch_4772_5, ch_4772_6, ch_4772_7])

theorem root_4779 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4779) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4779_0, decode 300 d_4779_1, decode 300 d_4779_2, decode 300 d_4779_3, decode 300 d_4779_4, decode 300 d_4779_5, decode 300 d_4779_6, decode 141 d_4779_7] (fun x hx => bits_full_and hx) cov_4779 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4779_0, ch_4779_1, ch_4779_2, ch_4779_3, ch_4779_4, ch_4779_5, ch_4779_6, ch_4779_7])

theorem root_4780 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4780) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4780_0, decode 300 d_4780_1, decode 300 d_4780_2, decode 300 d_4780_3, decode 300 d_4780_4, decode 300 d_4780_5, decode 300 d_4780_6, decode 141 d_4780_7] (fun x hx => bits_full_and hx) cov_4780 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4780_0, ch_4780_1, ch_4780_2, ch_4780_3, ch_4780_4, ch_4780_5, ch_4780_6, ch_4780_7])

theorem root_4781 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4781) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4781_0, decode 300 d_4781_1, decode 300 d_4781_2, decode 300 d_4781_3, decode 300 d_4781_4, decode 300 d_4781_5, decode 300 d_4781_6, decode 141 d_4781_7] (fun x hx => bits_full_and hx) cov_4781 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4781_0, ch_4781_1, ch_4781_2, ch_4781_3, ch_4781_4, ch_4781_5, ch_4781_6, ch_4781_7])

theorem root_4785 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4785) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4785_0, decode 300 d_4785_1, decode 300 d_4785_2, decode 300 d_4785_3, decode 300 d_4785_4, decode 300 d_4785_5, decode 300 d_4785_6, decode 142 d_4785_7] (fun x hx => bits_full_and hx) cov_4785 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4785_0, ch_4785_1, ch_4785_2, ch_4785_3, ch_4785_4, ch_4785_5, ch_4785_6, ch_4785_7])

theorem root_4787 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4787) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4787_0, decode 300 d_4787_1, decode 300 d_4787_2, decode 300 d_4787_3, decode 300 d_4787_4, decode 300 d_4787_5, decode 300 d_4787_6, decode 142 d_4787_7] (fun x hx => bits_full_and hx) cov_4787 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4787_0, ch_4787_1, ch_4787_2, ch_4787_3, ch_4787_4, ch_4787_5, ch_4787_6, ch_4787_7])

theorem root_4790 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4790) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4790_0, decode 300 d_4790_1, decode 300 d_4790_2, decode 300 d_4790_3, decode 300 d_4790_4, decode 300 d_4790_5, decode 80 d_4790_6] (fun x hx => bits_full_and hx) cov_4790 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4790_0, ch_4790_1, ch_4790_2, ch_4790_3, ch_4790_4, ch_4790_5, ch_4790_6])

theorem root_4791 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4791) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4791_0, decode 300 d_4791_1, decode 300 d_4791_2, decode 300 d_4791_3, decode 300 d_4791_4, decode 300 d_4791_5, decode 80 d_4791_6] (fun x hx => bits_full_and hx) cov_4791 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4791_0, ch_4791_1, ch_4791_2, ch_4791_3, ch_4791_4, ch_4791_5, ch_4791_6])

theorem root_4800 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4800) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4800_0, decode 300 d_4800_1, decode 300 d_4800_2, decode 300 d_4800_3, decode 300 d_4800_4, decode 300 d_4800_5, decode 300 d_4800_6, decode 141 d_4800_7] (fun x hx => bits_full_and hx) cov_4800 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4800_0, ch_4800_1, ch_4800_2, ch_4800_3, ch_4800_4, ch_4800_5, ch_4800_6, ch_4800_7])

theorem root_4803 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4803) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4803_0, decode 300 d_4803_1, decode 300 d_4803_2, decode 300 d_4803_3, decode 300 d_4803_4, decode 300 d_4803_5, decode 300 d_4803_6, decode 141 d_4803_7] (fun x hx => bits_full_and hx) cov_4803 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4803_0, ch_4803_1, ch_4803_2, ch_4803_3, ch_4803_4, ch_4803_5, ch_4803_6, ch_4803_7])

theorem root_4804 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4804) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4804_0, decode 300 d_4804_1, decode 300 d_4804_2, decode 300 d_4804_3, decode 300 d_4804_4, decode 300 d_4804_5, decode 300 d_4804_6, decode 141 d_4804_7] (fun x hx => bits_full_and hx) cov_4804 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4804_0, ch_4804_1, ch_4804_2, ch_4804_3, ch_4804_4, ch_4804_5, ch_4804_6, ch_4804_7])

theorem root_4808 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4808) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4808_0, decode 300 d_4808_1, decode 300 d_4808_2, decode 300 d_4808_3, decode 300 d_4808_4, decode 300 d_4808_5, decode 300 d_4808_6, decode 141 d_4808_7] (fun x hx => bits_full_and hx) cov_4808 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4808_0, ch_4808_1, ch_4808_2, ch_4808_3, ch_4808_4, ch_4808_5, ch_4808_6, ch_4808_7])

theorem roots_71_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_71, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_71, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_4749 hB hC hCl hCB, root_4761 hB hC hCl hCB, root_4762 hB hC hCl hCB, root_4763 hB hC hCl hCB, root_4764 hB hC hCl hCB, root_4770 hB hC hCl hCB, root_4771 hB hC hCl hCB, root_4772 hB hC hCl hCB, root_4779 hB hC hCl hCB, root_4780 hB hC hCl hCB, root_4781 hB hC hCl hCB, root_4785 hB hC hCl hCB, root_4787 hB hC hCl hCB, root_4790 hB hC hCl hCB, root_4791 hB hC hCl hCB, root_4800 hB hC hCl hCB, root_4803 hB hC hCl hCB, root_4804 hB hC hCl hCB, root_4808 hB hC hCl hCB]

theorem root_4811 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4811) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4811_0, decode 300 d_4811_1, decode 300 d_4811_2, decode 300 d_4811_3, decode 300 d_4811_4, decode 300 d_4811_5, decode 104 d_4811_6] (fun x hx => bits_full_and hx) cov_4811 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4811_0, ch_4811_1, ch_4811_2, ch_4811_3, ch_4811_4, ch_4811_5, ch_4811_6])

theorem root_4812 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4812) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4812_0, decode 300 d_4812_1, decode 300 d_4812_2, decode 300 d_4812_3, decode 300 d_4812_4, decode 300 d_4812_5, decode 79 d_4812_6] (fun x hx => bits_full_and hx) cov_4812 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4812_0, ch_4812_1, ch_4812_2, ch_4812_3, ch_4812_4, ch_4812_5, ch_4812_6])

theorem root_4816 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4816) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4816_0, decode 300 d_4816_1, decode 300 d_4816_2, decode 300 d_4816_3, decode 300 d_4816_4, decode 300 d_4816_5, decode 300 d_4816_6, decode 141 d_4816_7] (fun x hx => bits_full_and hx) cov_4816 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4816_0, ch_4816_1, ch_4816_2, ch_4816_3, ch_4816_4, ch_4816_5, ch_4816_6, ch_4816_7])

theorem root_4829 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4829) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4829_0, decode 300 d_4829_1, decode 300 d_4829_2, decode 300 d_4829_3, decode 300 d_4829_4, decode 300 d_4829_5, decode 300 d_4829_6, decode 141 d_4829_7] (fun x hx => bits_full_and hx) cov_4829 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4829_0, ch_4829_1, ch_4829_2, ch_4829_3, ch_4829_4, ch_4829_5, ch_4829_6, ch_4829_7])

theorem root_4839 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4839) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4839_0, decode 300 d_4839_1, decode 300 d_4839_2, decode 300 d_4839_3, decode 300 d_4839_4, decode 300 d_4839_5, decode 300 d_4839_6, decode 141 d_4839_7] (fun x hx => bits_full_and hx) cov_4839 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4839_0, ch_4839_1, ch_4839_2, ch_4839_3, ch_4839_4, ch_4839_5, ch_4839_6, ch_4839_7])

theorem root_4847 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4847) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4847_0, decode 300 d_4847_1, decode 300 d_4847_2, decode 300 d_4847_3, decode 300 d_4847_4, decode 300 d_4847_5, decode 300 d_4847_6, decode 141 d_4847_7] (fun x hx => bits_full_and hx) cov_4847 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4847_0, ch_4847_1, ch_4847_2, ch_4847_3, ch_4847_4, ch_4847_5, ch_4847_6, ch_4847_7])

theorem root_4853 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4853) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4853_0, decode 300 d_4853_1, decode 300 d_4853_2, decode 300 d_4853_3, decode 300 d_4853_4, decode 300 d_4853_5, decode 300 d_4853_6, decode 141 d_4853_7] (fun x hx => bits_full_and hx) cov_4853 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4853_0, ch_4853_1, ch_4853_2, ch_4853_3, ch_4853_4, ch_4853_5, ch_4853_6, ch_4853_7])

theorem root_4857 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4857) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4857_0, decode 300 d_4857_1, decode 300 d_4857_2, decode 300 d_4857_3, decode 300 d_4857_4, decode 300 d_4857_5, decode 104 d_4857_6] (fun x hx => bits_full_and hx) cov_4857 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4857_0, ch_4857_1, ch_4857_2, ch_4857_3, ch_4857_4, ch_4857_5, ch_4857_6])

theorem root_4858 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4858) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4858_0, decode 300 d_4858_1, decode 300 d_4858_2, decode 300 d_4858_3, decode 300 d_4858_4, decode 300 d_4858_5, decode 79 d_4858_6] (fun x hx => bits_full_and hx) cov_4858 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4858_0, ch_4858_1, ch_4858_2, ch_4858_3, ch_4858_4, ch_4858_5, ch_4858_6])

theorem root_4859 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4859) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4859_0, decode 300 d_4859_1, decode 300 d_4859_2, decode 300 d_4859_3, decode 300 d_4859_4, decode 300 d_4859_5, decode 79 d_4859_6] (fun x hx => bits_full_and hx) cov_4859 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4859_0, ch_4859_1, ch_4859_2, ch_4859_3, ch_4859_4, ch_4859_5, ch_4859_6])

theorem root_4868 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4868) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4868_0, decode 300 d_4868_1, decode 300 d_4868_2, decode 300 d_4868_3, decode 300 d_4868_4, decode 300 d_4868_5, decode 23 d_4868_6] (fun x hx => bits_full_and hx) cov_4868 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4868_0, ch_4868_1, ch_4868_2, ch_4868_3, ch_4868_4, ch_4868_5, ch_4868_6])

theorem root_4869 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4869) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4869_0, decode 300 d_4869_1, decode 300 d_4869_2, decode 300 d_4869_3, decode 300 d_4869_4, decode 300 d_4869_5, decode 23 d_4869_6] (fun x hx => bits_full_and hx) cov_4869 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4869_0, ch_4869_1, ch_4869_2, ch_4869_3, ch_4869_4, ch_4869_5, ch_4869_6])

theorem root_4875 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4875) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4875_0, decode 300 d_4875_1, decode 300 d_4875_2, decode 300 d_4875_3, decode 300 d_4875_4, decode 300 d_4875_5, decode 45 d_4875_6] (fun x hx => bits_full_and hx) cov_4875 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4875_0, ch_4875_1, ch_4875_2, ch_4875_3, ch_4875_4, ch_4875_5, ch_4875_6])

theorem root_4877 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4877) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4877_0, decode 300 d_4877_1, decode 300 d_4877_2, decode 300 d_4877_3, decode 300 d_4877_4, decode 300 d_4877_5, decode 6 d_4877_6] (fun x hx => bits_full_and hx) cov_4877 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4877_0, ch_4877_1, ch_4877_2, ch_4877_3, ch_4877_4, ch_4877_5, ch_4877_6])

theorem root_4880 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4880) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4880_0, decode 300 d_4880_1, decode 300 d_4880_2, decode 300 d_4880_3, decode 300 d_4880_4, decode 300 d_4880_5, decode 6 d_4880_6] (fun x hx => bits_full_and hx) cov_4880 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4880_0, ch_4880_1, ch_4880_2, ch_4880_3, ch_4880_4, ch_4880_5, ch_4880_6])

theorem root_4884 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4884) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4884_0, decode 300 d_4884_1, decode 300 d_4884_2, decode 300 d_4884_3, decode 300 d_4884_4, decode 300 d_4884_5, decode 157 d_4884_6] (fun x hx => bits_full_and hx) cov_4884 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4884_0, ch_4884_1, ch_4884_2, ch_4884_3, ch_4884_4, ch_4884_5, ch_4884_6])

theorem root_4888 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4888) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4888_0, decode 300 d_4888_1, decode 300 d_4888_2, decode 300 d_4888_3, decode 300 d_4888_4, decode 265 d_4888_5] (fun x hx => bits_full_and hx) cov_4888 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4888_0, ch_4888_1, ch_4888_2, ch_4888_3, ch_4888_4, ch_4888_5])

theorem root_4889 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4889) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4889_0, decode 300 d_4889_1, decode 300 d_4889_2, decode 300 d_4889_3, decode 300 d_4889_4, decode 265 d_4889_5] (fun x hx => bits_full_and hx) cov_4889 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4889_0, ch_4889_1, ch_4889_2, ch_4889_3, ch_4889_4, ch_4889_5])

theorem root_4894 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4894) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4894_0, decode 300 d_4894_1, decode 300 d_4894_2, decode 300 d_4894_3, decode 300 d_4894_4, decode 300 d_4894_5, decode 9 d_4894_6] (fun x hx => bits_full_and hx) cov_4894 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4894_0, ch_4894_1, ch_4894_2, ch_4894_3, ch_4894_4, ch_4894_5, ch_4894_6])

theorem root_4895 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4895) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4895_0, decode 300 d_4895_1, decode 300 d_4895_2, decode 300 d_4895_3, decode 300 d_4895_4, decode 213 d_4895_5] (fun x hx => bits_full_and hx) cov_4895 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4895_0, ch_4895_1, ch_4895_2, ch_4895_3, ch_4895_4, ch_4895_5])

theorem root_4901 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4901) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4901_0, decode 300 d_4901_1, decode 300 d_4901_2, decode 300 d_4901_3, decode 300 d_4901_4, decode 272 d_4901_5] (fun x hx => bits_full_and hx) cov_4901 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4901_0, ch_4901_1, ch_4901_2, ch_4901_3, ch_4901_4, ch_4901_5])

theorem roots_72_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_72, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_72, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_4811 hB hC hCl hCB, root_4812 hB hC hCl hCB, root_4816 hB hC hCl hCB, root_4829 hB hC hCl hCB, root_4839 hB hC hCl hCB, root_4847 hB hC hCl hCB, root_4853 hB hC hCl hCB, root_4857 hB hC hCl hCB, root_4858 hB hC hCl hCB, root_4859 hB hC hCl hCB, root_4868 hB hC hCl hCB, root_4869 hB hC hCl hCB, root_4875 hB hC hCl hCB, root_4877 hB hC hCl hCB, root_4880 hB hC hCl hCB, root_4884 hB hC hCl hCB, root_4888 hB hC hCl hCB, root_4889 hB hC hCl hCB, root_4894 hB hC hCl hCB, root_4895 hB hC hCl hCB, root_4901 hB hC hCl hCB]

theorem root_4902 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4902) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4902_0, decode 300 d_4902_1, decode 300 d_4902_2, decode 300 d_4902_3, decode 300 d_4902_4, decode 300 d_4902_5, decode 36 d_4902_6] (fun x hx => bits_full_and hx) cov_4902 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4902_0, ch_4902_1, ch_4902_2, ch_4902_3, ch_4902_4, ch_4902_5, ch_4902_6])

theorem root_4908 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4908) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4908_0, decode 300 d_4908_1, decode 300 d_4908_2, decode 300 d_4908_3, decode 300 d_4908_4, decode 300 d_4908_5, decode 9 d_4908_6] (fun x hx => bits_full_and hx) cov_4908 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4908_0, ch_4908_1, ch_4908_2, ch_4908_3, ch_4908_4, ch_4908_5, ch_4908_6])

theorem root_4909 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4909) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4909_0, decode 300 d_4909_1, decode 300 d_4909_2, decode 300 d_4909_3, decode 300 d_4909_4, decode 300 d_4909_5, decode 9 d_4909_6] (fun x hx => bits_full_and hx) cov_4909 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4909_0, ch_4909_1, ch_4909_2, ch_4909_3, ch_4909_4, ch_4909_5, ch_4909_6])

theorem root_4910 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4910) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4910_0, decode 300 d_4910_1, decode 300 d_4910_2, decode 300 d_4910_3, decode 300 d_4910_4, decode 199 d_4910_5] (fun x hx => bits_full_and hx) cov_4910 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4910_0, ch_4910_1, ch_4910_2, ch_4910_3, ch_4910_4, ch_4910_5])

theorem root_4918 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4918) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4918_0, decode 300 d_4918_1, decode 300 d_4918_2, decode 300 d_4918_3, decode 300 d_4918_4, decode 300 d_4918_5, decode 23 d_4918_6] (fun x hx => bits_full_and hx) cov_4918 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4918_0, ch_4918_1, ch_4918_2, ch_4918_3, ch_4918_4, ch_4918_5, ch_4918_6])

theorem root_4924 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4924) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4924_0, decode 300 d_4924_1, decode 300 d_4924_2, decode 300 d_4924_3, decode 300 d_4924_4, decode 300 d_4924_5, decode 300 d_4924_6, decode 141 d_4924_7] (fun x hx => bits_full_and hx) cov_4924 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4924_0, ch_4924_1, ch_4924_2, ch_4924_3, ch_4924_4, ch_4924_5, ch_4924_6, ch_4924_7])

theorem root_4927 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4927) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4927_0, decode 300 d_4927_1, decode 300 d_4927_2, decode 300 d_4927_3, decode 300 d_4927_4, decode 300 d_4927_5, decode 300 d_4927_6, decode 141 d_4927_7] (fun x hx => bits_full_and hx) cov_4927 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4927_0, ch_4927_1, ch_4927_2, ch_4927_3, ch_4927_4, ch_4927_5, ch_4927_6, ch_4927_7])

theorem root_4928 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4928) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4928_0, decode 300 d_4928_1, decode 300 d_4928_2, decode 300 d_4928_3, decode 300 d_4928_4, decode 300 d_4928_5, decode 300 d_4928_6, decode 158 d_4928_7] (fun x hx => bits_full_and hx) cov_4928 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4928_0, ch_4928_1, ch_4928_2, ch_4928_3, ch_4928_4, ch_4928_5, ch_4928_6, ch_4928_7])

theorem root_4934 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4934) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4934_0, decode 300 d_4934_1, decode 300 d_4934_2, decode 300 d_4934_3, decode 300 d_4934_4, decode 300 d_4934_5, decode 300 d_4934_6, decode 158 d_4934_7] (fun x hx => bits_full_and hx) cov_4934 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4934_0, ch_4934_1, ch_4934_2, ch_4934_3, ch_4934_4, ch_4934_5, ch_4934_6, ch_4934_7])

theorem root_4935 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4935) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4935_0, decode 300 d_4935_1, decode 300 d_4935_2, decode 300 d_4935_3, decode 300 d_4935_4, decode 300 d_4935_5, decode 300 d_4935_6, decode 158 d_4935_7] (fun x hx => bits_full_and hx) cov_4935 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4935_0, ch_4935_1, ch_4935_2, ch_4935_3, ch_4935_4, ch_4935_5, ch_4935_6, ch_4935_7])

theorem root_4947 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4947) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4947_0, decode 300 d_4947_1, decode 300 d_4947_2, decode 300 d_4947_3, decode 300 d_4947_4, decode 300 d_4947_5, decode 300 d_4947_6, decode 141 d_4947_7] (fun x hx => bits_full_and hx) cov_4947 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4947_0, ch_4947_1, ch_4947_2, ch_4947_3, ch_4947_4, ch_4947_5, ch_4947_6, ch_4947_7])

theorem root_4948 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4948) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4948_0, decode 300 d_4948_1, decode 300 d_4948_2, decode 300 d_4948_3, decode 300 d_4948_4, decode 300 d_4948_5, decode 300 d_4948_6, decode 141 d_4948_7] (fun x hx => bits_full_and hx) cov_4948 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4948_0, ch_4948_1, ch_4948_2, ch_4948_3, ch_4948_4, ch_4948_5, ch_4948_6, ch_4948_7])

theorem root_4949 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4949) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4949_0, decode 300 d_4949_1, decode 300 d_4949_2, decode 300 d_4949_3, decode 300 d_4949_4, decode 300 d_4949_5, decode 300 d_4949_6, decode 141 d_4949_7] (fun x hx => bits_full_and hx) cov_4949 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4949_0, ch_4949_1, ch_4949_2, ch_4949_3, ch_4949_4, ch_4949_5, ch_4949_6, ch_4949_7])

theorem root_4950 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4950) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4950_0, decode 300 d_4950_1, decode 300 d_4950_2, decode 300 d_4950_3, decode 300 d_4950_4, decode 300 d_4950_5, decode 300 d_4950_6, decode 141 d_4950_7] (fun x hx => bits_full_and hx) cov_4950 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4950_0, ch_4950_1, ch_4950_2, ch_4950_3, ch_4950_4, ch_4950_5, ch_4950_6, ch_4950_7])

theorem root_4951 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4951) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4951_0, decode 300 d_4951_1, decode 300 d_4951_2, decode 300 d_4951_3, decode 300 d_4951_4, decode 300 d_4951_5, decode 300 d_4951_6, decode 141 d_4951_7] (fun x hx => bits_full_and hx) cov_4951 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4951_0, ch_4951_1, ch_4951_2, ch_4951_3, ch_4951_4, ch_4951_5, ch_4951_6, ch_4951_7])

theorem root_4952 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4952) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4952_0, decode 300 d_4952_1, decode 300 d_4952_2, decode 300 d_4952_3, decode 300 d_4952_4, decode 300 d_4952_5, decode 300 d_4952_6, decode 141 d_4952_7] (fun x hx => bits_full_and hx) cov_4952 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4952_0, ch_4952_1, ch_4952_2, ch_4952_3, ch_4952_4, ch_4952_5, ch_4952_6, ch_4952_7])

theorem root_4959 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4959) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4959_0, decode 300 d_4959_1, decode 300 d_4959_2, decode 300 d_4959_3, decode 300 d_4959_4, decode 300 d_4959_5, decode 300 d_4959_6, decode 142 d_4959_7] (fun x hx => bits_full_and hx) cov_4959 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4959_0, ch_4959_1, ch_4959_2, ch_4959_3, ch_4959_4, ch_4959_5, ch_4959_6, ch_4959_7])

theorem root_4962 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4962) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4962_0, decode 300 d_4962_1, decode 300 d_4962_2, decode 300 d_4962_3, decode 300 d_4962_4, decode 300 d_4962_5, decode 300 d_4962_6, decode 142 d_4962_7] (fun x hx => bits_full_and hx) cov_4962 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4962_0, ch_4962_1, ch_4962_2, ch_4962_3, ch_4962_4, ch_4962_5, ch_4962_6, ch_4962_7])

theorem root_4971 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4971) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4971_0, decode 300 d_4971_1, decode 300 d_4971_2, decode 300 d_4971_3, decode 300 d_4971_4, decode 300 d_4971_5, decode 300 d_4971_6, decode 142 d_4971_7] (fun x hx => bits_full_and hx) cov_4971 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4971_0, ch_4971_1, ch_4971_2, ch_4971_3, ch_4971_4, ch_4971_5, ch_4971_6, ch_4971_7])

theorem roots_73_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_73, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_73, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_4902 hB hC hCl hCB, root_4908 hB hC hCl hCB, root_4909 hB hC hCl hCB, root_4910 hB hC hCl hCB, root_4918 hB hC hCl hCB, root_4924 hB hC hCl hCB, root_4927 hB hC hCl hCB, root_4928 hB hC hCl hCB, root_4934 hB hC hCl hCB, root_4935 hB hC hCl hCB, root_4947 hB hC hCl hCB, root_4948 hB hC hCl hCB, root_4949 hB hC hCl hCB, root_4950 hB hC hCl hCB, root_4951 hB hC hCl hCB, root_4952 hB hC hCl hCB, root_4959 hB hC hCl hCB, root_4962 hB hC hCl hCB, root_4971 hB hC hCl hCB]

theorem root_4977 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4977) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4977_0, decode 300 d_4977_1, decode 300 d_4977_2, decode 300 d_4977_3, decode 300 d_4977_4, decode 300 d_4977_5, decode 300 d_4977_6, decode 141 d_4977_7] (fun x hx => bits_full_and hx) cov_4977 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4977_0, ch_4977_1, ch_4977_2, ch_4977_3, ch_4977_4, ch_4977_5, ch_4977_6, ch_4977_7])

theorem root_4978 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4978) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4978_0, decode 300 d_4978_1, decode 300 d_4978_2, decode 300 d_4978_3, decode 300 d_4978_4, decode 300 d_4978_5, decode 300 d_4978_6, decode 142 d_4978_7] (fun x hx => bits_full_and hx) cov_4978 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4978_0, ch_4978_1, ch_4978_2, ch_4978_3, ch_4978_4, ch_4978_5, ch_4978_6, ch_4978_7])

theorem root_4979 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4979) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4979_0, decode 300 d_4979_1, decode 300 d_4979_2, decode 300 d_4979_3, decode 300 d_4979_4, decode 300 d_4979_5, decode 300 d_4979_6, decode 142 d_4979_7] (fun x hx => bits_full_and hx) cov_4979 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4979_0, ch_4979_1, ch_4979_2, ch_4979_3, ch_4979_4, ch_4979_5, ch_4979_6, ch_4979_7])

theorem root_4985 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4985) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4985_0, decode 300 d_4985_1, decode 300 d_4985_2, decode 300 d_4985_3, decode 300 d_4985_4, decode 300 d_4985_5, decode 300 d_4985_6, decode 141 d_4985_7] (fun x hx => bits_full_and hx) cov_4985 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4985_0, ch_4985_1, ch_4985_2, ch_4985_3, ch_4985_4, ch_4985_5, ch_4985_6, ch_4985_7])

theorem root_4986 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4986) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4986_0, decode 300 d_4986_1, decode 300 d_4986_2, decode 300 d_4986_3, decode 300 d_4986_4, decode 300 d_4986_5, decode 300 d_4986_6, decode 142 d_4986_7] (fun x hx => bits_full_and hx) cov_4986 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4986_0, ch_4986_1, ch_4986_2, ch_4986_3, ch_4986_4, ch_4986_5, ch_4986_6, ch_4986_7])

theorem root_4987 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4987) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4987_0, decode 300 d_4987_1, decode 300 d_4987_2, decode 300 d_4987_3, decode 300 d_4987_4, decode 300 d_4987_5, decode 300 d_4987_6, decode 142 d_4987_7] (fun x hx => bits_full_and hx) cov_4987 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4987_0, ch_4987_1, ch_4987_2, ch_4987_3, ch_4987_4, ch_4987_5, ch_4987_6, ch_4987_7])

theorem root_4994 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 4994) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_4994_0, decode 300 d_4994_1, decode 300 d_4994_2, decode 300 d_4994_3, decode 300 d_4994_4, decode 300 d_4994_5, decode 53 d_4994_6] (fun x hx => bits_full_and hx) cov_4994 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_4994_0, ch_4994_1, ch_4994_2, ch_4994_3, ch_4994_4, ch_4994_5, ch_4994_6])

theorem root_5005 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5005) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5005_0, decode 300 d_5005_1, decode 300 d_5005_2, decode 300 d_5005_3, decode 300 d_5005_4, decode 286 d_5005_5] (fun x hx => bits_full_and hx) cov_5005 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5005_0, ch_5005_1, ch_5005_2, ch_5005_3, ch_5005_4, ch_5005_5])

theorem root_5010 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5010) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5010_0, decode 300 d_5010_1, decode 300 d_5010_2, decode 300 d_5010_3, decode 300 d_5010_4, decode 300 d_5010_5, decode 35 d_5010_6] (fun x hx => bits_full_and hx) cov_5010 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5010_0, ch_5010_1, ch_5010_2, ch_5010_3, ch_5010_4, ch_5010_5, ch_5010_6])

theorem root_5016 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5016) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5016_0, decode 300 d_5016_1, decode 300 d_5016_2, decode 300 d_5016_3, decode 300 d_5016_4, decode 300 d_5016_5, decode 300 d_5016_6, decode 142 d_5016_7] (fun x hx => bits_full_and hx) cov_5016 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5016_0, ch_5016_1, ch_5016_2, ch_5016_3, ch_5016_4, ch_5016_5, ch_5016_6, ch_5016_7])

theorem root_5025 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5025) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5025_0, decode 300 d_5025_1, decode 300 d_5025_2, decode 300 d_5025_3, decode 300 d_5025_4, decode 300 d_5025_5, decode 300 d_5025_6, decode 142 d_5025_7] (fun x hx => bits_full_and hx) cov_5025 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5025_0, ch_5025_1, ch_5025_2, ch_5025_3, ch_5025_4, ch_5025_5, ch_5025_6, ch_5025_7])

theorem root_5032 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5032) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5032_0, decode 300 d_5032_1, decode 300 d_5032_2, decode 300 d_5032_3, decode 300 d_5032_4, decode 300 d_5032_5, decode 300 d_5032_6, decode 142 d_5032_7] (fun x hx => bits_full_and hx) cov_5032 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5032_0, ch_5032_1, ch_5032_2, ch_5032_3, ch_5032_4, ch_5032_5, ch_5032_6, ch_5032_7])

theorem root_5034 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5034) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5034_0, decode 300 d_5034_1, decode 300 d_5034_2, decode 300 d_5034_3, decode 300 d_5034_4, decode 300 d_5034_5, decode 300 d_5034_6, decode 142 d_5034_7] (fun x hx => bits_full_and hx) cov_5034 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5034_0, ch_5034_1, ch_5034_2, ch_5034_3, ch_5034_4, ch_5034_5, ch_5034_6, ch_5034_7])

theorem root_5040 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5040) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5040_0, decode 300 d_5040_1, decode 300 d_5040_2, decode 300 d_5040_3, decode 300 d_5040_4, decode 300 d_5040_5, decode 54 d_5040_6] (fun x hx => bits_full_and hx) cov_5040 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5040_0, ch_5040_1, ch_5040_2, ch_5040_3, ch_5040_4, ch_5040_5, ch_5040_6])

theorem root_5044 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5044) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5044_0, decode 300 d_5044_1, decode 300 d_5044_2, decode 300 d_5044_3, decode 300 d_5044_4, decode 300 d_5044_5, decode 54 d_5044_6] (fun x hx => bits_full_and hx) cov_5044 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5044_0, ch_5044_1, ch_5044_2, ch_5044_3, ch_5044_4, ch_5044_5, ch_5044_6])

theorem root_5045 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5045) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5045_0, decode 300 d_5045_1, decode 300 d_5045_2, decode 300 d_5045_3, decode 300 d_5045_4, decode 300 d_5045_5, decode 54 d_5045_6] (fun x hx => bits_full_and hx) cov_5045 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5045_0, ch_5045_1, ch_5045_2, ch_5045_3, ch_5045_4, ch_5045_5, ch_5045_6])

theorem root_5049 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5049) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5049_0, decode 300 d_5049_1, decode 300 d_5049_2, decode 300 d_5049_3, decode 300 d_5049_4, decode 300 d_5049_5, decode 54 d_5049_6] (fun x hx => bits_full_and hx) cov_5049 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5049_0, ch_5049_1, ch_5049_2, ch_5049_3, ch_5049_4, ch_5049_5, ch_5049_6])

theorem root_5063 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5063) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5063_0, decode 300 d_5063_1, decode 300 d_5063_2, decode 300 d_5063_3, decode 300 d_5063_4, decode 300 d_5063_5, decode 300 d_5063_6, decode 158 d_5063_7] (fun x hx => bits_full_and hx) cov_5063 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5063_0, ch_5063_1, ch_5063_2, ch_5063_3, ch_5063_4, ch_5063_5, ch_5063_6, ch_5063_7])

theorem root_5064 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5064) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5064_0, decode 300 d_5064_1, decode 300 d_5064_2, decode 300 d_5064_3, decode 300 d_5064_4, decode 300 d_5064_5, decode 300 d_5064_6, decode 158 d_5064_7] (fun x hx => bits_full_and hx) cov_5064 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5064_0, ch_5064_1, ch_5064_2, ch_5064_3, ch_5064_4, ch_5064_5, ch_5064_6, ch_5064_7])

theorem root_5073 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5073) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5073_0, decode 300 d_5073_1, decode 300 d_5073_2, decode 300 d_5073_3, decode 300 d_5073_4, decode 300 d_5073_5, decode 300 d_5073_6, decode 141 d_5073_7] (fun x hx => bits_full_and hx) cov_5073 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5073_0, ch_5073_1, ch_5073_2, ch_5073_3, ch_5073_4, ch_5073_5, ch_5073_6, ch_5073_7])

theorem roots_74_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_74, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_74, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_4977 hB hC hCl hCB, root_4978 hB hC hCl hCB, root_4979 hB hC hCl hCB, root_4985 hB hC hCl hCB, root_4986 hB hC hCl hCB, root_4987 hB hC hCl hCB, root_4994 hB hC hCl hCB, root_5005 hB hC hCl hCB, root_5010 hB hC hCl hCB, root_5016 hB hC hCl hCB, root_5025 hB hC hCl hCB, root_5032 hB hC hCl hCB, root_5034 hB hC hCl hCB, root_5040 hB hC hCl hCB, root_5044 hB hC hCl hCB, root_5045 hB hC hCl hCB, root_5049 hB hC hCl hCB, root_5063 hB hC hCl hCB, root_5064 hB hC hCl hCB, root_5073 hB hC hCl hCB]

theorem root_5074 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5074) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5074_0, decode 300 d_5074_1, decode 300 d_5074_2, decode 300 d_5074_3, decode 300 d_5074_4, decode 300 d_5074_5, decode 300 d_5074_6, decode 141 d_5074_7] (fun x hx => bits_full_and hx) cov_5074 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5074_0, ch_5074_1, ch_5074_2, ch_5074_3, ch_5074_4, ch_5074_5, ch_5074_6, ch_5074_7])

theorem root_5078 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5078) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5078_0, decode 300 d_5078_1, decode 300 d_5078_2, decode 300 d_5078_3, decode 300 d_5078_4, decode 300 d_5078_5, decode 300 d_5078_6, decode 142 d_5078_7] (fun x hx => bits_full_and hx) cov_5078 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5078_0, ch_5078_1, ch_5078_2, ch_5078_3, ch_5078_4, ch_5078_5, ch_5078_6, ch_5078_7])

theorem root_5086 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5086) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5086_0, decode 300 d_5086_1, decode 300 d_5086_2, decode 300 d_5086_3, decode 300 d_5086_4, decode 300 d_5086_5, decode 300 d_5086_6, decode 158 d_5086_7] (fun x hx => bits_full_and hx) cov_5086 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5086_0, ch_5086_1, ch_5086_2, ch_5086_3, ch_5086_4, ch_5086_5, ch_5086_6, ch_5086_7])

theorem root_5087 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5087) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5087_0, decode 300 d_5087_1, decode 300 d_5087_2, decode 300 d_5087_3, decode 300 d_5087_4, decode 300 d_5087_5, decode 300 d_5087_6, decode 158 d_5087_7] (fun x hx => bits_full_and hx) cov_5087 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5087_0, ch_5087_1, ch_5087_2, ch_5087_3, ch_5087_4, ch_5087_5, ch_5087_6, ch_5087_7])

theorem root_5088 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5088) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5088_0, decode 300 d_5088_1, decode 300 d_5088_2, decode 300 d_5088_3, decode 300 d_5088_4, decode 300 d_5088_5, decode 300 d_5088_6, decode 158 d_5088_7] (fun x hx => bits_full_and hx) cov_5088 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5088_0, ch_5088_1, ch_5088_2, ch_5088_3, ch_5088_4, ch_5088_5, ch_5088_6, ch_5088_7])

theorem root_5094 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5094) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5094_0, decode 300 d_5094_1, decode 300 d_5094_2, decode 300 d_5094_3, decode 300 d_5094_4, decode 300 d_5094_5, decode 300 d_5094_6, decode 141 d_5094_7] (fun x hx => bits_full_and hx) cov_5094 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5094_0, ch_5094_1, ch_5094_2, ch_5094_3, ch_5094_4, ch_5094_5, ch_5094_6, ch_5094_7])

theorem root_5095 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5095) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5095_0, decode 300 d_5095_1, decode 300 d_5095_2, decode 300 d_5095_3, decode 300 d_5095_4, decode 300 d_5095_5, decode 300 d_5095_6, decode 141 d_5095_7] (fun x hx => bits_full_and hx) cov_5095 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5095_0, ch_5095_1, ch_5095_2, ch_5095_3, ch_5095_4, ch_5095_5, ch_5095_6, ch_5095_7])

theorem root_5096 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5096) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5096_0, decode 300 d_5096_1, decode 300 d_5096_2, decode 300 d_5096_3, decode 300 d_5096_4, decode 300 d_5096_5, decode 300 d_5096_6, decode 141 d_5096_7] (fun x hx => bits_full_and hx) cov_5096 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5096_0, ch_5096_1, ch_5096_2, ch_5096_3, ch_5096_4, ch_5096_5, ch_5096_6, ch_5096_7])

theorem root_5098 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5098) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5098_0, decode 300 d_5098_1, decode 300 d_5098_2, decode 300 d_5098_3, decode 300 d_5098_4, decode 300 d_5098_5, decode 300 d_5098_6, decode 141 d_5098_7] (fun x hx => bits_full_and hx) cov_5098 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5098_0, ch_5098_1, ch_5098_2, ch_5098_3, ch_5098_4, ch_5098_5, ch_5098_6, ch_5098_7])

theorem root_5099 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5099) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5099_0, decode 300 d_5099_1, decode 300 d_5099_2, decode 300 d_5099_3, decode 300 d_5099_4, decode 300 d_5099_5, decode 300 d_5099_6, decode 158 d_5099_7] (fun x hx => bits_full_and hx) cov_5099 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5099_0, ch_5099_1, ch_5099_2, ch_5099_3, ch_5099_4, ch_5099_5, ch_5099_6, ch_5099_7])

theorem root_5100 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5100) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5100_0, decode 300 d_5100_1, decode 300 d_5100_2, decode 300 d_5100_3, decode 300 d_5100_4, decode 300 d_5100_5, decode 300 d_5100_6, decode 158 d_5100_7] (fun x hx => bits_full_and hx) cov_5100 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5100_0, ch_5100_1, ch_5100_2, ch_5100_3, ch_5100_4, ch_5100_5, ch_5100_6, ch_5100_7])

theorem root_5101 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5101) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5101_0, decode 300 d_5101_1, decode 300 d_5101_2, decode 300 d_5101_3, decode 300 d_5101_4, decode 300 d_5101_5, decode 300 d_5101_6, decode 158 d_5101_7] (fun x hx => bits_full_and hx) cov_5101 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5101_0, ch_5101_1, ch_5101_2, ch_5101_3, ch_5101_4, ch_5101_5, ch_5101_6, ch_5101_7])

theorem root_5112 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5112) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5112_0, decode 300 d_5112_1, decode 300 d_5112_2, decode 300 d_5112_3, decode 300 d_5112_4, decode 300 d_5112_5, decode 300 d_5112_6, decode 141 d_5112_7] (fun x hx => bits_full_and hx) cov_5112 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5112_0, ch_5112_1, ch_5112_2, ch_5112_3, ch_5112_4, ch_5112_5, ch_5112_6, ch_5112_7])

theorem root_5113 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5113) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5113_0, decode 300 d_5113_1, decode 300 d_5113_2, decode 300 d_5113_3, decode 300 d_5113_4, decode 300 d_5113_5, decode 300 d_5113_6, decode 141 d_5113_7] (fun x hx => bits_full_and hx) cov_5113 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5113_0, ch_5113_1, ch_5113_2, ch_5113_3, ch_5113_4, ch_5113_5, ch_5113_6, ch_5113_7])

theorem root_5114 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5114) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5114_0, decode 300 d_5114_1, decode 300 d_5114_2, decode 300 d_5114_3, decode 300 d_5114_4, decode 300 d_5114_5, decode 300 d_5114_6, decode 141 d_5114_7] (fun x hx => bits_full_and hx) cov_5114 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5114_0, ch_5114_1, ch_5114_2, ch_5114_3, ch_5114_4, ch_5114_5, ch_5114_6, ch_5114_7])

theorem root_5115 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5115) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5115_0, decode 300 d_5115_1, decode 300 d_5115_2, decode 300 d_5115_3, decode 300 d_5115_4, decode 300 d_5115_5, decode 300 d_5115_6, decode 141 d_5115_7] (fun x hx => bits_full_and hx) cov_5115 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5115_0, ch_5115_1, ch_5115_2, ch_5115_3, ch_5115_4, ch_5115_5, ch_5115_6, ch_5115_7])

theorem root_5130 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5130) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5130_0, decode 300 d_5130_1, decode 300 d_5130_2, decode 300 d_5130_3, decode 300 d_5130_4, decode 300 d_5130_5, decode 300 d_5130_6, decode 141 d_5130_7] (fun x hx => bits_full_and hx) cov_5130 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5130_0, ch_5130_1, ch_5130_2, ch_5130_3, ch_5130_4, ch_5130_5, ch_5130_6, ch_5130_7])

theorem root_5131 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5131) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5131_0, decode 300 d_5131_1, decode 300 d_5131_2, decode 300 d_5131_3, decode 300 d_5131_4, decode 300 d_5131_5, decode 300 d_5131_6, decode 141 d_5131_7] (fun x hx => bits_full_and hx) cov_5131 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5131_0, ch_5131_1, ch_5131_2, ch_5131_3, ch_5131_4, ch_5131_5, ch_5131_6, ch_5131_7])

theorem roots_75_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_75, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_75, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_5074 hB hC hCl hCB, root_5078 hB hC hCl hCB, root_5086 hB hC hCl hCB, root_5087 hB hC hCl hCB, root_5088 hB hC hCl hCB, root_5094 hB hC hCl hCB, root_5095 hB hC hCl hCB, root_5096 hB hC hCl hCB, root_5098 hB hC hCl hCB, root_5099 hB hC hCl hCB, root_5100 hB hC hCl hCB, root_5101 hB hC hCl hCB, root_5112 hB hC hCl hCB, root_5113 hB hC hCl hCB, root_5114 hB hC hCl hCB, root_5115 hB hC hCl hCB, root_5130 hB hC hCl hCB, root_5131 hB hC hCl hCB]

theorem root_5132 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5132) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5132_0, decode 300 d_5132_1, decode 300 d_5132_2, decode 300 d_5132_3, decode 300 d_5132_4, decode 300 d_5132_5, decode 300 d_5132_6, decode 141 d_5132_7] (fun x hx => bits_full_and hx) cov_5132 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5132_0, ch_5132_1, ch_5132_2, ch_5132_3, ch_5132_4, ch_5132_5, ch_5132_6, ch_5132_7])

theorem root_5133 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5133) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5133_0, decode 300 d_5133_1, decode 300 d_5133_2, decode 300 d_5133_3, decode 300 d_5133_4, decode 300 d_5133_5, decode 300 d_5133_6, decode 141 d_5133_7] (fun x hx => bits_full_and hx) cov_5133 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5133_0, ch_5133_1, ch_5133_2, ch_5133_3, ch_5133_4, ch_5133_5, ch_5133_6, ch_5133_7])

theorem root_5134 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5134) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5134_0, decode 300 d_5134_1, decode 300 d_5134_2, decode 300 d_5134_3, decode 300 d_5134_4, decode 300 d_5134_5, decode 300 d_5134_6, decode 141 d_5134_7] (fun x hx => bits_full_and hx) cov_5134 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5134_0, ch_5134_1, ch_5134_2, ch_5134_3, ch_5134_4, ch_5134_5, ch_5134_6, ch_5134_7])

theorem root_5137 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5137) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5137_0, decode 300 d_5137_1, decode 300 d_5137_2, decode 300 d_5137_3, decode 300 d_5137_4, decode 300 d_5137_5, decode 300 d_5137_6, decode 142 d_5137_7] (fun x hx => bits_full_and hx) cov_5137 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5137_0, ch_5137_1, ch_5137_2, ch_5137_3, ch_5137_4, ch_5137_5, ch_5137_6, ch_5137_7])

theorem root_5138 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5138) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5138_0, decode 300 d_5138_1, decode 300 d_5138_2, decode 300 d_5138_3, decode 300 d_5138_4, decode 300 d_5138_5, decode 300 d_5138_6, decode 141 d_5138_7] (fun x hx => bits_full_and hx) cov_5138 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5138_0, ch_5138_1, ch_5138_2, ch_5138_3, ch_5138_4, ch_5138_5, ch_5138_6, ch_5138_7])

theorem root_5143 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5143) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5143_0, decode 300 d_5143_1, decode 300 d_5143_2, decode 300 d_5143_3, decode 300 d_5143_4, decode 300 d_5143_5, decode 300 d_5143_6, decode 142 d_5143_7] (fun x hx => bits_full_and hx) cov_5143 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5143_0, ch_5143_1, ch_5143_2, ch_5143_3, ch_5143_4, ch_5143_5, ch_5143_6, ch_5143_7])

theorem root_5144 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5144) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5144_0, decode 300 d_5144_1, decode 300 d_5144_2, decode 300 d_5144_3, decode 300 d_5144_4, decode 300 d_5144_5, decode 300 d_5144_6, decode 142 d_5144_7] (fun x hx => bits_full_and hx) cov_5144 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5144_0, ch_5144_1, ch_5144_2, ch_5144_3, ch_5144_4, ch_5144_5, ch_5144_6, ch_5144_7])

theorem root_5145 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5145) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5145_0, decode 300 d_5145_1, decode 300 d_5145_2, decode 300 d_5145_3, decode 300 d_5145_4, decode 300 d_5145_5, decode 300 d_5145_6, decode 141 d_5145_7] (fun x hx => bits_full_and hx) cov_5145 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5145_0, ch_5145_1, ch_5145_2, ch_5145_3, ch_5145_4, ch_5145_5, ch_5145_6, ch_5145_7])

theorem root_5150 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5150) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5150_0, decode 300 d_5150_1, decode 300 d_5150_2, decode 300 d_5150_3, decode 300 d_5150_4, decode 300 d_5150_5, decode 300 d_5150_6, decode 141 d_5150_7] (fun x hx => bits_full_and hx) cov_5150 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5150_0, ch_5150_1, ch_5150_2, ch_5150_3, ch_5150_4, ch_5150_5, ch_5150_6, ch_5150_7])

theorem root_5151 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5151) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5151_0, decode 300 d_5151_1, decode 300 d_5151_2, decode 300 d_5151_3, decode 300 d_5151_4, decode 300 d_5151_5, decode 300 d_5151_6, decode 141 d_5151_7] (fun x hx => bits_full_and hx) cov_5151 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5151_0, ch_5151_1, ch_5151_2, ch_5151_3, ch_5151_4, ch_5151_5, ch_5151_6, ch_5151_7])

theorem root_5152 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5152) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5152_0, decode 300 d_5152_1, decode 300 d_5152_2, decode 300 d_5152_3, decode 300 d_5152_4, decode 300 d_5152_5, decode 300 d_5152_6, decode 158 d_5152_7] (fun x hx => bits_full_and hx) cov_5152 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5152_0, ch_5152_1, ch_5152_2, ch_5152_3, ch_5152_4, ch_5152_5, ch_5152_6, ch_5152_7])

theorem root_5153 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5153) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5153_0, decode 300 d_5153_1, decode 300 d_5153_2, decode 300 d_5153_3, decode 300 d_5153_4, decode 300 d_5153_5, decode 300 d_5153_6, decode 158 d_5153_7] (fun x hx => bits_full_and hx) cov_5153 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5153_0, ch_5153_1, ch_5153_2, ch_5153_3, ch_5153_4, ch_5153_5, ch_5153_6, ch_5153_7])

theorem root_5158 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5158) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5158_0, decode 300 d_5158_1, decode 300 d_5158_2, decode 300 d_5158_3, decode 300 d_5158_4, decode 300 d_5158_5, decode 300 d_5158_6, decode 141 d_5158_7] (fun x hx => bits_full_and hx) cov_5158 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5158_0, ch_5158_1, ch_5158_2, ch_5158_3, ch_5158_4, ch_5158_5, ch_5158_6, ch_5158_7])

theorem root_5164 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5164) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5164_0, decode 300 d_5164_1, decode 300 d_5164_2, decode 300 d_5164_3, decode 300 d_5164_4, decode 300 d_5164_5, decode 300 d_5164_6, decode 158 d_5164_7] (fun x hx => bits_full_and hx) cov_5164 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5164_0, ch_5164_1, ch_5164_2, ch_5164_3, ch_5164_4, ch_5164_5, ch_5164_6, ch_5164_7])

theorem root_5168 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5168) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5168_0, decode 300 d_5168_1, decode 300 d_5168_2, decode 300 d_5168_3, decode 300 d_5168_4, decode 300 d_5168_5, decode 300 d_5168_6, decode 141 d_5168_7] (fun x hx => bits_full_and hx) cov_5168 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5168_0, ch_5168_1, ch_5168_2, ch_5168_3, ch_5168_4, ch_5168_5, ch_5168_6, ch_5168_7])

theorem root_5169 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5169) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5169_0, decode 300 d_5169_1, decode 300 d_5169_2, decode 300 d_5169_3, decode 300 d_5169_4, decode 300 d_5169_5, decode 300 d_5169_6, decode 158 d_5169_7] (fun x hx => bits_full_and hx) cov_5169 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5169_0, ch_5169_1, ch_5169_2, ch_5169_3, ch_5169_4, ch_5169_5, ch_5169_6, ch_5169_7])

theorem root_5173 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5173) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5173_0, decode 300 d_5173_1, decode 300 d_5173_2, decode 300 d_5173_3, decode 300 d_5173_4, decode 300 d_5173_5, decode 300 d_5173_6, decode 141 d_5173_7] (fun x hx => bits_full_and hx) cov_5173 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5173_0, ch_5173_1, ch_5173_2, ch_5173_3, ch_5173_4, ch_5173_5, ch_5173_6, ch_5173_7])

theorem root_5174 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5174) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5174_0, decode 300 d_5174_1, decode 300 d_5174_2, decode 300 d_5174_3, decode 300 d_5174_4, decode 300 d_5174_5, decode 300 d_5174_6, decode 141 d_5174_7] (fun x hx => bits_full_and hx) cov_5174 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5174_0, ch_5174_1, ch_5174_2, ch_5174_3, ch_5174_4, ch_5174_5, ch_5174_6, ch_5174_7])

theorem roots_76_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_76, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_76, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_5132 hB hC hCl hCB, root_5133 hB hC hCl hCB, root_5134 hB hC hCl hCB, root_5137 hB hC hCl hCB, root_5138 hB hC hCl hCB, root_5143 hB hC hCl hCB, root_5144 hB hC hCl hCB, root_5145 hB hC hCl hCB, root_5150 hB hC hCl hCB, root_5151 hB hC hCl hCB, root_5152 hB hC hCl hCB, root_5153 hB hC hCl hCB, root_5158 hB hC hCl hCB, root_5164 hB hC hCl hCB, root_5168 hB hC hCl hCB, root_5169 hB hC hCl hCB, root_5173 hB hC hCl hCB, root_5174 hB hC hCl hCB]

theorem root_5175 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5175) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5175_0, decode 300 d_5175_1, decode 300 d_5175_2, decode 300 d_5175_3, decode 300 d_5175_4, decode 300 d_5175_5, decode 300 d_5175_6, decode 158 d_5175_7] (fun x hx => bits_full_and hx) cov_5175 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5175_0, ch_5175_1, ch_5175_2, ch_5175_3, ch_5175_4, ch_5175_5, ch_5175_6, ch_5175_7])

theorem root_5176 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5176) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5176_0, decode 300 d_5176_1, decode 300 d_5176_2, decode 300 d_5176_3, decode 300 d_5176_4, decode 300 d_5176_5, decode 300 d_5176_6, decode 158 d_5176_7] (fun x hx => bits_full_and hx) cov_5176 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5176_0, ch_5176_1, ch_5176_2, ch_5176_3, ch_5176_4, ch_5176_5, ch_5176_6, ch_5176_7])

theorem root_5181 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5181) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5181_0, decode 300 d_5181_1, decode 300 d_5181_2, decode 300 d_5181_3, decode 300 d_5181_4, decode 300 d_5181_5, decode 300 d_5181_6, decode 141 d_5181_7] (fun x hx => bits_full_and hx) cov_5181 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5181_0, ch_5181_1, ch_5181_2, ch_5181_3, ch_5181_4, ch_5181_5, ch_5181_6, ch_5181_7])

theorem root_5182 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5182) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5182_0, decode 300 d_5182_1, decode 300 d_5182_2, decode 300 d_5182_3, decode 300 d_5182_4, decode 300 d_5182_5, decode 300 d_5182_6, decode 141 d_5182_7] (fun x hx => bits_full_and hx) cov_5182 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5182_0, ch_5182_1, ch_5182_2, ch_5182_3, ch_5182_4, ch_5182_5, ch_5182_6, ch_5182_7])

theorem root_5183 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5183) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5183_0, decode 300 d_5183_1, decode 300 d_5183_2, decode 300 d_5183_3, decode 300 d_5183_4, decode 300 d_5183_5, decode 300 d_5183_6, decode 158 d_5183_7] (fun x hx => bits_full_and hx) cov_5183 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5183_0, ch_5183_1, ch_5183_2, ch_5183_3, ch_5183_4, ch_5183_5, ch_5183_6, ch_5183_7])

theorem root_5184 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5184) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5184_0, decode 300 d_5184_1, decode 300 d_5184_2, decode 300 d_5184_3, decode 300 d_5184_4, decode 300 d_5184_5, decode 300 d_5184_6, decode 158 d_5184_7] (fun x hx => bits_full_and hx) cov_5184 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5184_0, ch_5184_1, ch_5184_2, ch_5184_3, ch_5184_4, ch_5184_5, ch_5184_6, ch_5184_7])

theorem root_5188 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5188) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5188_0, decode 300 d_5188_1, decode 300 d_5188_2, decode 300 d_5188_3, decode 300 d_5188_4, decode 300 d_5188_5, decode 300 d_5188_6, decode 141 d_5188_7] (fun x hx => bits_full_and hx) cov_5188 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5188_0, ch_5188_1, ch_5188_2, ch_5188_3, ch_5188_4, ch_5188_5, ch_5188_6, ch_5188_7])

theorem root_5189 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5189) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5189_0, decode 300 d_5189_1, decode 300 d_5189_2, decode 300 d_5189_3, decode 300 d_5189_4, decode 300 d_5189_5, decode 300 d_5189_6, decode 141 d_5189_7] (fun x hx => bits_full_and hx) cov_5189 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5189_0, ch_5189_1, ch_5189_2, ch_5189_3, ch_5189_4, ch_5189_5, ch_5189_6, ch_5189_7])

theorem root_5190 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5190) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5190_0, decode 300 d_5190_1, decode 300 d_5190_2, decode 300 d_5190_3, decode 300 d_5190_4, decode 300 d_5190_5, decode 300 d_5190_6, decode 158 d_5190_7] (fun x hx => bits_full_and hx) cov_5190 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5190_0, ch_5190_1, ch_5190_2, ch_5190_3, ch_5190_4, ch_5190_5, ch_5190_6, ch_5190_7])

theorem root_5191 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5191) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5191_0, decode 300 d_5191_1, decode 300 d_5191_2, decode 300 d_5191_3, decode 300 d_5191_4, decode 300 d_5191_5, decode 300 d_5191_6, decode 158 d_5191_7] (fun x hx => bits_full_and hx) cov_5191 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5191_0, ch_5191_1, ch_5191_2, ch_5191_3, ch_5191_4, ch_5191_5, ch_5191_6, ch_5191_7])

theorem root_5196 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5196) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5196_0, decode 300 d_5196_1, decode 300 d_5196_2, decode 300 d_5196_3, decode 300 d_5196_4, decode 300 d_5196_5, decode 300 d_5196_6, decode 142 d_5196_7] (fun x hx => bits_full_and hx) cov_5196 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5196_0, ch_5196_1, ch_5196_2, ch_5196_3, ch_5196_4, ch_5196_5, ch_5196_6, ch_5196_7])

theorem root_5197 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5197) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5197_0, decode 300 d_5197_1, decode 300 d_5197_2, decode 300 d_5197_3, decode 300 d_5197_4, decode 300 d_5197_5, decode 300 d_5197_6, decode 142 d_5197_7] (fun x hx => bits_full_and hx) cov_5197 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5197_0, ch_5197_1, ch_5197_2, ch_5197_3, ch_5197_4, ch_5197_5, ch_5197_6, ch_5197_7])

theorem root_5198 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5198) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5198_0, decode 300 d_5198_1, decode 300 d_5198_2, decode 300 d_5198_3, decode 300 d_5198_4, decode 300 d_5198_5, decode 300 d_5198_6, decode 141 d_5198_7] (fun x hx => bits_full_and hx) cov_5198 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5198_0, ch_5198_1, ch_5198_2, ch_5198_3, ch_5198_4, ch_5198_5, ch_5198_6, ch_5198_7])

theorem root_5211 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5211) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5211_0, decode 300 d_5211_1, decode 300 d_5211_2, decode 300 d_5211_3, decode 300 d_5211_4, decode 300 d_5211_5, decode 100 d_5211_6] (fun x hx => bits_full_and hx) cov_5211 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5211_0, ch_5211_1, ch_5211_2, ch_5211_3, ch_5211_4, ch_5211_5, ch_5211_6])

theorem root_5213 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5213) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5213_0, decode 300 d_5213_1, decode 300 d_5213_2, decode 300 d_5213_3, decode 300 d_5213_4, decode 300 d_5213_5, decode 6 d_5213_6] (fun x hx => bits_full_and hx) cov_5213 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5213_0, ch_5213_1, ch_5213_2, ch_5213_3, ch_5213_4, ch_5213_5, ch_5213_6])

theorem root_5217 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5217) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5217_0, decode 300 d_5217_1, decode 300 d_5217_2, decode 300 d_5217_3, decode 300 d_5217_4, decode 300 d_5217_5, decode 100 d_5217_6] (fun x hx => bits_full_and hx) cov_5217 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5217_0, ch_5217_1, ch_5217_2, ch_5217_3, ch_5217_4, ch_5217_5, ch_5217_6])

theorem root_5218 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5218) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5218_0, decode 300 d_5218_1, decode 300 d_5218_2, decode 300 d_5218_3, decode 300 d_5218_4, decode 300 d_5218_5, decode 100 d_5218_6] (fun x hx => bits_full_and hx) cov_5218 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5218_0, ch_5218_1, ch_5218_2, ch_5218_3, ch_5218_4, ch_5218_5, ch_5218_6])

theorem root_5220 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5220) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5220_0, decode 300 d_5220_1, decode 300 d_5220_2, decode 300 d_5220_3, decode 300 d_5220_4, decode 300 d_5220_5, decode 300 d_5220_6, decode 141 d_5220_7] (fun x hx => bits_full_and hx) cov_5220 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5220_0, ch_5220_1, ch_5220_2, ch_5220_3, ch_5220_4, ch_5220_5, ch_5220_6, ch_5220_7])

theorem root_5221 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5221) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5221_0, decode 300 d_5221_1, decode 300 d_5221_2, decode 300 d_5221_3, decode 300 d_5221_4, decode 300 d_5221_5, decode 300 d_5221_6, decode 141 d_5221_7] (fun x hx => bits_full_and hx) cov_5221 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5221_0, ch_5221_1, ch_5221_2, ch_5221_3, ch_5221_4, ch_5221_5, ch_5221_6, ch_5221_7])

theorem roots_77_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_77, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_77, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_5175 hB hC hCl hCB, root_5176 hB hC hCl hCB, root_5181 hB hC hCl hCB, root_5182 hB hC hCl hCB, root_5183 hB hC hCl hCB, root_5184 hB hC hCl hCB, root_5188 hB hC hCl hCB, root_5189 hB hC hCl hCB, root_5190 hB hC hCl hCB, root_5191 hB hC hCl hCB, root_5196 hB hC hCl hCB, root_5197 hB hC hCl hCB, root_5198 hB hC hCl hCB, root_5211 hB hC hCl hCB, root_5213 hB hC hCl hCB, root_5217 hB hC hCl hCB, root_5218 hB hC hCl hCB, root_5220 hB hC hCl hCB, root_5221 hB hC hCl hCB]

theorem root_5226 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5226) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5226_0, decode 300 d_5226_1, decode 300 d_5226_2, decode 300 d_5226_3, decode 300 d_5226_4, decode 300 d_5226_5, decode 300 d_5226_6, decode 142 d_5226_7] (fun x hx => bits_full_and hx) cov_5226 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5226_0, ch_5226_1, ch_5226_2, ch_5226_3, ch_5226_4, ch_5226_5, ch_5226_6, ch_5226_7])

theorem root_5227 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5227) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5227_0, decode 300 d_5227_1, decode 300 d_5227_2, decode 300 d_5227_3, decode 300 d_5227_4, decode 300 d_5227_5, decode 300 d_5227_6, decode 142 d_5227_7] (fun x hx => bits_full_and hx) cov_5227 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5227_0, ch_5227_1, ch_5227_2, ch_5227_3, ch_5227_4, ch_5227_5, ch_5227_6, ch_5227_7])

theorem root_5230 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5230) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5230_0, decode 300 d_5230_1, decode 300 d_5230_2, decode 300 d_5230_3, decode 300 d_5230_4, decode 300 d_5230_5, decode 300 d_5230_6, decode 141 d_5230_7] (fun x hx => bits_full_and hx) cov_5230 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5230_0, ch_5230_1, ch_5230_2, ch_5230_3, ch_5230_4, ch_5230_5, ch_5230_6, ch_5230_7])

theorem root_5231 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5231) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5231_0, decode 300 d_5231_1, decode 300 d_5231_2, decode 300 d_5231_3, decode 300 d_5231_4, decode 300 d_5231_5, decode 300 d_5231_6, decode 141 d_5231_7] (fun x hx => bits_full_and hx) cov_5231 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5231_0, ch_5231_1, ch_5231_2, ch_5231_3, ch_5231_4, ch_5231_5, ch_5231_6, ch_5231_7])

theorem root_5234 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5234) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5234_0, decode 300 d_5234_1, decode 300 d_5234_2, decode 300 d_5234_3, decode 300 d_5234_4, decode 300 d_5234_5, decode 300 d_5234_6, decode 142 d_5234_7] (fun x hx => bits_full_and hx) cov_5234 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5234_0, ch_5234_1, ch_5234_2, ch_5234_3, ch_5234_4, ch_5234_5, ch_5234_6, ch_5234_7])

theorem root_5238 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5238) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5238_0, decode 300 d_5238_1, decode 300 d_5238_2, decode 300 d_5238_3, decode 300 d_5238_4, decode 300 d_5238_5, decode 300 d_5238_6, decode 142 d_5238_7] (fun x hx => bits_full_and hx) cov_5238 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5238_0, ch_5238_1, ch_5238_2, ch_5238_3, ch_5238_4, ch_5238_5, ch_5238_6, ch_5238_7])

theorem root_5239 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5239) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5239_0, decode 300 d_5239_1, decode 300 d_5239_2, decode 300 d_5239_3, decode 300 d_5239_4, decode 300 d_5239_5, decode 300 d_5239_6, decode 141 d_5239_7] (fun x hx => bits_full_and hx) cov_5239 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5239_0, ch_5239_1, ch_5239_2, ch_5239_3, ch_5239_4, ch_5239_5, ch_5239_6, ch_5239_7])

theorem root_5245 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5245) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5245_0, decode 300 d_5245_1, decode 300 d_5245_2, decode 300 d_5245_3, decode 300 d_5245_4, decode 300 d_5245_5, decode 300 d_5245_6, decode 142 d_5245_7] (fun x hx => bits_full_and hx) cov_5245 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5245_0, ch_5245_1, ch_5245_2, ch_5245_3, ch_5245_4, ch_5245_5, ch_5245_6, ch_5245_7])

theorem root_5247 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5247) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5247_0, decode 300 d_5247_1, decode 300 d_5247_2, decode 300 d_5247_3, decode 300 d_5247_4, decode 300 d_5247_5, decode 300 d_5247_6, decode 141 d_5247_7] (fun x hx => bits_full_and hx) cov_5247 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5247_0, ch_5247_1, ch_5247_2, ch_5247_3, ch_5247_4, ch_5247_5, ch_5247_6, ch_5247_7])

theorem root_5248 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5248) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5248_0, decode 300 d_5248_1, decode 300 d_5248_2, decode 300 d_5248_3, decode 300 d_5248_4, decode 300 d_5248_5, decode 300 d_5248_6, decode 141 d_5248_7] (fun x hx => bits_full_and hx) cov_5248 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5248_0, ch_5248_1, ch_5248_2, ch_5248_3, ch_5248_4, ch_5248_5, ch_5248_6, ch_5248_7])

theorem root_5250 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5250) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5250_0, decode 300 d_5250_1, decode 300 d_5250_2, decode 300 d_5250_3, decode 300 d_5250_4, decode 300 d_5250_5, decode 300 d_5250_6, decode 141 d_5250_7] (fun x hx => bits_full_and hx) cov_5250 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5250_0, ch_5250_1, ch_5250_2, ch_5250_3, ch_5250_4, ch_5250_5, ch_5250_6, ch_5250_7])

theorem root_5262 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5262) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5262_0, decode 300 d_5262_1, decode 300 d_5262_2, decode 300 d_5262_3, decode 300 d_5262_4, decode 300 d_5262_5, decode 300 d_5262_6, decode 141 d_5262_7] (fun x hx => bits_full_and hx) cov_5262 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5262_0, ch_5262_1, ch_5262_2, ch_5262_3, ch_5262_4, ch_5262_5, ch_5262_6, ch_5262_7])

theorem root_5263 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5263) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5263_0, decode 300 d_5263_1, decode 300 d_5263_2, decode 300 d_5263_3, decode 300 d_5263_4, decode 300 d_5263_5, decode 300 d_5263_6, decode 141 d_5263_7] (fun x hx => bits_full_and hx) cov_5263 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5263_0, ch_5263_1, ch_5263_2, ch_5263_3, ch_5263_4, ch_5263_5, ch_5263_6, ch_5263_7])

theorem root_5264 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5264) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5264_0, decode 300 d_5264_1, decode 300 d_5264_2, decode 300 d_5264_3, decode 300 d_5264_4, decode 300 d_5264_5, decode 300 d_5264_6, decode 141 d_5264_7] (fun x hx => bits_full_and hx) cov_5264 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5264_0, ch_5264_1, ch_5264_2, ch_5264_3, ch_5264_4, ch_5264_5, ch_5264_6, ch_5264_7])

theorem root_5270 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5270) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5270_0, decode 300 d_5270_1, decode 300 d_5270_2, decode 300 d_5270_3, decode 300 d_5270_4, decode 300 d_5270_5, decode 70 d_5270_6] (fun x hx => bits_full_and hx) cov_5270 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5270_0, ch_5270_1, ch_5270_2, ch_5270_3, ch_5270_4, ch_5270_5, ch_5270_6])

theorem root_5271 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5271) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5271_0, decode 300 d_5271_1, decode 300 d_5271_2, decode 300 d_5271_3, decode 300 d_5271_4, decode 300 d_5271_5, decode 11 d_5271_6] (fun x hx => bits_full_and hx) cov_5271 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5271_0, ch_5271_1, ch_5271_2, ch_5271_3, ch_5271_4, ch_5271_5, ch_5271_6])

theorem root_5274 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5274) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5274_0, decode 300 d_5274_1, decode 300 d_5274_2, decode 300 d_5274_3, decode 300 d_5274_4, decode 300 d_5274_5, decode 300 d_5274_6, decode 141 d_5274_7] (fun x hx => bits_full_and hx) cov_5274 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5274_0, ch_5274_1, ch_5274_2, ch_5274_3, ch_5274_4, ch_5274_5, ch_5274_6, ch_5274_7])

theorem root_5275 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5275) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5275_0, decode 300 d_5275_1, decode 300 d_5275_2, decode 300 d_5275_3, decode 300 d_5275_4, decode 300 d_5275_5, decode 300 d_5275_6, decode 141 d_5275_7] (fun x hx => bits_full_and hx) cov_5275 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5275_0, ch_5275_1, ch_5275_2, ch_5275_3, ch_5275_4, ch_5275_5, ch_5275_6, ch_5275_7])

theorem root_5279 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5279) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5279_0, decode 300 d_5279_1, decode 300 d_5279_2, decode 300 d_5279_3, decode 300 d_5279_4, decode 300 d_5279_5, decode 300 d_5279_6, decode 142 d_5279_7] (fun x hx => bits_full_and hx) cov_5279 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5279_0, ch_5279_1, ch_5279_2, ch_5279_3, ch_5279_4, ch_5279_5, ch_5279_6, ch_5279_7])

theorem roots_78_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_78, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_78, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_5226 hB hC hCl hCB, root_5227 hB hC hCl hCB, root_5230 hB hC hCl hCB, root_5231 hB hC hCl hCB, root_5234 hB hC hCl hCB, root_5238 hB hC hCl hCB, root_5239 hB hC hCl hCB, root_5245 hB hC hCl hCB, root_5247 hB hC hCl hCB, root_5248 hB hC hCl hCB, root_5250 hB hC hCl hCB, root_5262 hB hC hCl hCB, root_5263 hB hC hCl hCB, root_5264 hB hC hCl hCB, root_5270 hB hC hCl hCB, root_5271 hB hC hCl hCB, root_5274 hB hC hCl hCB, root_5275 hB hC hCl hCB, root_5279 hB hC hCl hCB]

theorem root_5285 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5285) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5285_0, decode 300 d_5285_1, decode 300 d_5285_2, decode 300 d_5285_3, decode 300 d_5285_4, decode 300 d_5285_5, decode 300 d_5285_6, decode 141 d_5285_7] (fun x hx => bits_full_and hx) cov_5285 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5285_0, ch_5285_1, ch_5285_2, ch_5285_3, ch_5285_4, ch_5285_5, ch_5285_6, ch_5285_7])

theorem root_5287 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5287) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5287_0, decode 300 d_5287_1, decode 300 d_5287_2, decode 300 d_5287_3, decode 300 d_5287_4, decode 300 d_5287_5, decode 300 d_5287_6, decode 142 d_5287_7] (fun x hx => bits_full_and hx) cov_5287 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5287_0, ch_5287_1, ch_5287_2, ch_5287_3, ch_5287_4, ch_5287_5, ch_5287_6, ch_5287_7])

theorem root_5294 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5294) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5294_0, decode 300 d_5294_1, decode 300 d_5294_2, decode 300 d_5294_3, decode 300 d_5294_4, decode 300 d_5294_5, decode 12 d_5294_6] (fun x hx => bits_full_and hx) cov_5294 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5294_0, ch_5294_1, ch_5294_2, ch_5294_3, ch_5294_4, ch_5294_5, ch_5294_6])

theorem root_5295 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5295) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5295_0, decode 300 d_5295_1, decode 300 d_5295_2, decode 300 d_5295_3, decode 300 d_5295_4, decode 300 d_5295_5, decode 179 d_5295_6] (fun x hx => bits_full_and hx) cov_5295 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5295_0, ch_5295_1, ch_5295_2, ch_5295_3, ch_5295_4, ch_5295_5, ch_5295_6])

theorem root_5300 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5300) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5300_0, decode 300 d_5300_1, decode 300 d_5300_2, decode 300 d_5300_3, decode 300 d_5300_4, decode 300 d_5300_5, decode 117 d_5300_6] (fun x hx => bits_full_and hx) cov_5300 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5300_0, ch_5300_1, ch_5300_2, ch_5300_3, ch_5300_4, ch_5300_5, ch_5300_6])

theorem root_5302 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5302) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5302_0, decode 300 d_5302_1, decode 300 d_5302_2, decode 300 d_5302_3, decode 300 d_5302_4, decode 300 d_5302_5, decode 300 d_5302_6, decode 141 d_5302_7] (fun x hx => bits_full_and hx) cov_5302 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5302_0, ch_5302_1, ch_5302_2, ch_5302_3, ch_5302_4, ch_5302_5, ch_5302_6, ch_5302_7])

theorem root_5308 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5308) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5308_0, decode 300 d_5308_1, decode 300 d_5308_2, decode 300 d_5308_3, decode 300 d_5308_4, decode 300 d_5308_5, decode 300 d_5308_6, decode 142 d_5308_7] (fun x hx => bits_full_and hx) cov_5308 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5308_0, ch_5308_1, ch_5308_2, ch_5308_3, ch_5308_4, ch_5308_5, ch_5308_6, ch_5308_7])

theorem root_5310 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5310) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5310_0, decode 300 d_5310_1, decode 300 d_5310_2, decode 300 d_5310_3, decode 300 d_5310_4, decode 300 d_5310_5, decode 300 d_5310_6, decode 141 d_5310_7] (fun x hx => bits_full_and hx) cov_5310 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5310_0, ch_5310_1, ch_5310_2, ch_5310_3, ch_5310_4, ch_5310_5, ch_5310_6, ch_5310_7])

theorem root_5311 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5311) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5311_0, decode 300 d_5311_1, decode 300 d_5311_2, decode 300 d_5311_3, decode 300 d_5311_4, decode 300 d_5311_5, decode 300 d_5311_6, decode 141 d_5311_7] (fun x hx => bits_full_and hx) cov_5311 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5311_0, ch_5311_1, ch_5311_2, ch_5311_3, ch_5311_4, ch_5311_5, ch_5311_6, ch_5311_7])

theorem root_5317 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5317) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5317_0, decode 300 d_5317_1, decode 300 d_5317_2, decode 300 d_5317_3, decode 300 d_5317_4, decode 300 d_5317_5, decode 300 d_5317_6, decode 141 d_5317_7] (fun x hx => bits_full_and hx) cov_5317 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5317_0, ch_5317_1, ch_5317_2, ch_5317_3, ch_5317_4, ch_5317_5, ch_5317_6, ch_5317_7])

theorem root_5318 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5318) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5318_0, decode 300 d_5318_1, decode 300 d_5318_2, decode 300 d_5318_3, decode 300 d_5318_4, decode 300 d_5318_5, decode 300 d_5318_6, decode 141 d_5318_7] (fun x hx => bits_full_and hx) cov_5318 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5318_0, ch_5318_1, ch_5318_2, ch_5318_3, ch_5318_4, ch_5318_5, ch_5318_6, ch_5318_7])

theorem root_5321 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5321) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5321_0, decode 300 d_5321_1, decode 300 d_5321_2, decode 300 d_5321_3, decode 300 d_5321_4, decode 300 d_5321_5, decode 300 d_5321_6, decode 141 d_5321_7] (fun x hx => bits_full_and hx) cov_5321 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5321_0, ch_5321_1, ch_5321_2, ch_5321_3, ch_5321_4, ch_5321_5, ch_5321_6, ch_5321_7])

theorem root_5322 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5322) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5322_0, decode 300 d_5322_1, decode 300 d_5322_2, decode 300 d_5322_3, decode 300 d_5322_4, decode 300 d_5322_5, decode 300 d_5322_6, decode 141 d_5322_7] (fun x hx => bits_full_and hx) cov_5322 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5322_0, ch_5322_1, ch_5322_2, ch_5322_3, ch_5322_4, ch_5322_5, ch_5322_6, ch_5322_7])

theorem root_5323 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5323) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5323_0, decode 300 d_5323_1, decode 300 d_5323_2, decode 300 d_5323_3, decode 300 d_5323_4, decode 300 d_5323_5, decode 300 d_5323_6, decode 141 d_5323_7] (fun x hx => bits_full_and hx) cov_5323 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5323_0, ch_5323_1, ch_5323_2, ch_5323_3, ch_5323_4, ch_5323_5, ch_5323_6, ch_5323_7])

theorem root_5324 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5324) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5324_0, decode 300 d_5324_1, decode 300 d_5324_2, decode 300 d_5324_3, decode 300 d_5324_4, decode 300 d_5324_5, decode 300 d_5324_6, decode 141 d_5324_7] (fun x hx => bits_full_and hx) cov_5324 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5324_0, ch_5324_1, ch_5324_2, ch_5324_3, ch_5324_4, ch_5324_5, ch_5324_6, ch_5324_7])

theorem root_5325 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5325) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5325_0, decode 300 d_5325_1, decode 300 d_5325_2, decode 300 d_5325_3, decode 300 d_5325_4, decode 300 d_5325_5, decode 300 d_5325_6, decode 141 d_5325_7] (fun x hx => bits_full_and hx) cov_5325 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5325_0, ch_5325_1, ch_5325_2, ch_5325_3, ch_5325_4, ch_5325_5, ch_5325_6, ch_5325_7])

theorem root_5334 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5334) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5334_0, decode 300 d_5334_1, decode 300 d_5334_2, decode 300 d_5334_3, decode 300 d_5334_4, decode 300 d_5334_5, decode 300 d_5334_6, decode 141 d_5334_7] (fun x hx => bits_full_and hx) cov_5334 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5334_0, ch_5334_1, ch_5334_2, ch_5334_3, ch_5334_4, ch_5334_5, ch_5334_6, ch_5334_7])

theorem root_5335 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5335) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5335_0, decode 300 d_5335_1, decode 300 d_5335_2, decode 300 d_5335_3, decode 300 d_5335_4, decode 300 d_5335_5, decode 300 d_5335_6, decode 141 d_5335_7] (fun x hx => bits_full_and hx) cov_5335 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5335_0, ch_5335_1, ch_5335_2, ch_5335_3, ch_5335_4, ch_5335_5, ch_5335_6, ch_5335_7])

theorem root_5336 (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    Claim (FULL &&& MT 5336) 3 :=
  claim_three_of_chunks hB hC hCl hCB [decode 300 d_5336_0, decode 300 d_5336_1, decode 300 d_5336_2, decode 300 d_5336_3, decode 300 d_5336_4, decode 300 d_5336_5, decode 300 d_5336_6, decode 141 d_5336_7] (fun x hx => bits_full_and hx) cov_5336 (by
    intro ch hch
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hch
    rcases hch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ch_5336_0, ch_5336_1, ch_5336_2, ch_5336_3, ch_5336_4, ch_5336_5, ch_5336_6, ch_5336_7])

theorem roots_79_ok (hB : BlkSpec) (hC : CapSpec) (hCl : ClassSpec) (hCB : CBSpec) :
    ∀ k ∈ roots_79, Claim (FULL &&& MT k) 3 := by
  intro k hk
  simp only [roots_79, List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [root_5285 hB hC hCl hCB, root_5287 hB hC hCl hCB, root_5294 hB hC hCl hCB, root_5295 hB hC hCl hCB, root_5300 hB hC hCl hCB, root_5302 hB hC hCl hCB, root_5308 hB hC hCl hCB, root_5310 hB hC hCl hCB, root_5311 hB hC hCl hCB, root_5317 hB hC hCl hCB, root_5318 hB hC hCl hCB, root_5321 hB hC hCl hCB, root_5322 hB hC hCl hCB, root_5323 hB hC hCl hCB, root_5324 hB hC hCl hCB, root_5325 hB hC hCl hCB, root_5334 hB hC hCl hCB, root_5335 hB hC hCl hCB, root_5336 hB hC hCl hCB]

end LRC.O7U5
