import Fresh.M4ZoneAssembly
import Fresh.ChainZone.S_0
import Fresh.ChainZone.S_1
import Fresh.ChainZone.S_2
import Fresh.ChainZone.S_3
import Fresh.ChainZone.S_4
import Fresh.ChainZone.S_5
import Fresh.ChainZone.S_6
import Fresh.ChainZone.S_7

/-!
# `ChainBoxSoundPinned`, proved (2026-11-22)

New file.  The 73 chain boxes, each covered by a gap-pattern zone certificate with `w = 1`
(`Fresh/ChainZone/S_k.lean`, kernel-checked); `chainPinned_of_zone` does the rest.

Covering form [PROVISIONAL: covering -- supports "every reading vector of a chain box has a
clear instant R in [1,7] or [9,15]"]: each box lies in the union of the gap-pattern zones C_m.
The Lean proof assumes no covering: every cut is a case split by le_total and every leaf is
an exact inclusion.  The place: R = max_r (8 m_r + 1)/g_r, the last gap entry over the readings.
-/

namespace Fresh.ChainZone
open Fresh.ZoneCover Fresh.M4SplitAssembly Fresh.M4ZoneAssembly Fresh.FilterAssemblyPerBox
open Fresh.FilterAssemblyPerBoxV2

theorem chainBoxSoundPinned_proved : ChainBoxSoundPinned := by
  refine chainPinned_of_zone ?_
  intro t ht
  simp only [chainBoxes, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, cz_0⟩
  · exact ⟨_, cz_1⟩
  · exact ⟨_, cz_2⟩
  · exact ⟨_, cz_3⟩
  · exact ⟨_, cz_4⟩
  · exact ⟨_, cz_5⟩
  · exact ⟨_, cz_6⟩
  · exact ⟨_, cz_7⟩
  · exact ⟨_, cz_8⟩
  · exact ⟨_, cz_9⟩
  · exact ⟨_, cz_10⟩
  · exact ⟨_, cz_11⟩
  · exact ⟨_, cz_12⟩
  · exact ⟨_, cz_13⟩
  · exact ⟨_, cz_14⟩
  · exact ⟨_, cz_15⟩
  · exact ⟨_, cz_16⟩
  · exact ⟨_, cz_17⟩
  · exact ⟨_, cz_18⟩
  · exact ⟨_, cz_19⟩
  · exact ⟨_, cz_20⟩
  · exact ⟨_, cz_21⟩
  · exact ⟨_, cz_22⟩
  · exact ⟨_, cz_23⟩
  · exact ⟨_, cz_24⟩
  · exact ⟨_, cz_25⟩
  · exact ⟨_, cz_26⟩
  · exact ⟨_, cz_27⟩
  · exact ⟨_, cz_28⟩
  · exact ⟨_, cz_29⟩
  · exact ⟨_, cz_30⟩
  · exact ⟨_, cz_31⟩
  · exact ⟨_, cz_32⟩
  · exact ⟨_, cz_33⟩
  · exact ⟨_, cz_34⟩
  · exact ⟨_, cz_35⟩
  · exact ⟨_, cz_36⟩
  · exact ⟨_, cz_37⟩
  · exact ⟨_, cz_38⟩
  · exact ⟨_, cz_39⟩
  · exact ⟨_, cz_40⟩
  · exact ⟨_, cz_41⟩
  · exact ⟨_, cz_42⟩
  · exact ⟨_, cz_43⟩
  · exact ⟨_, cz_44⟩
  · exact ⟨_, cz_45⟩
  · exact ⟨_, cz_46⟩
  · exact ⟨_, cz_47⟩
  · exact ⟨_, cz_48⟩
  · exact ⟨_, cz_49⟩
  · exact ⟨_, cz_50⟩
  · exact ⟨_, cz_51⟩
  · exact ⟨_, cz_52⟩
  · exact ⟨_, cz_53⟩
  · exact ⟨_, cz_54⟩
  · exact ⟨_, cz_55⟩
  · exact ⟨_, cz_56⟩
  · exact ⟨_, cz_57⟩
  · exact ⟨_, cz_58⟩
  · exact ⟨_, cz_59⟩
  · exact ⟨_, cz_60⟩
  · exact ⟨_, cz_61⟩
  · exact ⟨_, cz_62⟩
  · exact ⟨_, cz_63⟩
  · exact ⟨_, cz_64⟩
  · exact ⟨_, cz_65⟩
  · exact ⟨_, cz_66⟩
  · exact ⟨_, cz_67⟩
  · exact ⟨_, cz_68⟩
  · exact ⟨_, cz_69⟩
  · exact ⟨_, cz_70⟩
  · exact ⟨_, cz_71⟩
  · exact ⟨_, cz_72⟩

#print axioms chainBoxSoundPinned_proved

end Fresh.ChainZone
