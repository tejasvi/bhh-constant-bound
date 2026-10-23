/-
Kernel-only proof: the g table `gtK 5` (BHHCert/GTabK.lean) is sound, `gtK_sound_five : GTabSound 5 (gtK 5)`, by kernel
evaluation (`decide +kernel`, no `native_decide`) of the local check `localOK` (BHH/GraphK5/Local.lean) on 32 ranges
of edge states (BHH/GraphK5/C00-C31.lean); soundness of the local check: BHH/GraphK5/Sound.lean.
-/
import BHH.GraphK5.Sound
import BHH.GraphK5.C00
import BHH.GraphK5.C01
import BHH.GraphK5.C02
import BHH.GraphK5.C03
import BHH.GraphK5.C04
import BHH.GraphK5.C05
import BHH.GraphK5.C06
import BHH.GraphK5.C07
import BHH.GraphK5.C08
import BHH.GraphK5.C09
import BHH.GraphK5.C10
import BHH.GraphK5.C11
import BHH.GraphK5.C12
import BHH.GraphK5.C13
import BHH.GraphK5.C14
import BHH.GraphK5.C15
import BHH.GraphK5.C16
import BHH.GraphK5.C17
import BHH.GraphK5.C18
import BHH.GraphK5.C19
import BHH.GraphK5.C20
import BHH.GraphK5.C21
import BHH.GraphK5.C22
import BHH.GraphK5.C23
import BHH.GraphK5.C24
import BHH.GraphK5.C25
import BHH.GraphK5.C26
import BHH.GraphK5.C27
import BHH.GraphK5.C28
import BHH.GraphK5.C29
import BHH.GraphK5.C30
import BHH.GraphK5.C31

namespace BHH.E

open BHH.Cert

theorem gtK_local_five : ∀ idx < 3 ^ (pairList 5).length, localOK 5 (gtK 5).gmin idx = true := by
  have h01 : localRange 5 (gtK 5).gmin 0 3692 = true := localRange_add' gtK5_c00 gtK5_c01 rfl rfl
  have h02 : localRange 5 (gtK 5).gmin 0 5538 = true := localRange_add' h01 gtK5_c02 rfl rfl
  have h03 : localRange 5 (gtK 5).gmin 0 7384 = true := localRange_add' h02 gtK5_c03 rfl rfl
  have h04 : localRange 5 (gtK 5).gmin 0 9230 = true := localRange_add' h03 gtK5_c04 rfl rfl
  have h05 : localRange 5 (gtK 5).gmin 0 11076 = true := localRange_add' h04 gtK5_c05 rfl rfl
  have h06 : localRange 5 (gtK 5).gmin 0 12922 = true := localRange_add' h05 gtK5_c06 rfl rfl
  have h07 : localRange 5 (gtK 5).gmin 0 14768 = true := localRange_add' h06 gtK5_c07 rfl rfl
  have h08 : localRange 5 (gtK 5).gmin 0 16614 = true := localRange_add' h07 gtK5_c08 rfl rfl
  have h09 : localRange 5 (gtK 5).gmin 0 18460 = true := localRange_add' h08 gtK5_c09 rfl rfl
  have h10 : localRange 5 (gtK 5).gmin 0 20306 = true := localRange_add' h09 gtK5_c10 rfl rfl
  have h11 : localRange 5 (gtK 5).gmin 0 22152 = true := localRange_add' h10 gtK5_c11 rfl rfl
  have h12 : localRange 5 (gtK 5).gmin 0 23998 = true := localRange_add' h11 gtK5_c12 rfl rfl
  have h13 : localRange 5 (gtK 5).gmin 0 25844 = true := localRange_add' h12 gtK5_c13 rfl rfl
  have h14 : localRange 5 (gtK 5).gmin 0 27690 = true := localRange_add' h13 gtK5_c14 rfl rfl
  have h15 : localRange 5 (gtK 5).gmin 0 29536 = true := localRange_add' h14 gtK5_c15 rfl rfl
  have h16 : localRange 5 (gtK 5).gmin 0 31382 = true := localRange_add' h15 gtK5_c16 rfl rfl
  have h17 : localRange 5 (gtK 5).gmin 0 33228 = true := localRange_add' h16 gtK5_c17 rfl rfl
  have h18 : localRange 5 (gtK 5).gmin 0 35074 = true := localRange_add' h17 gtK5_c18 rfl rfl
  have h19 : localRange 5 (gtK 5).gmin 0 36920 = true := localRange_add' h18 gtK5_c19 rfl rfl
  have h20 : localRange 5 (gtK 5).gmin 0 38766 = true := localRange_add' h19 gtK5_c20 rfl rfl
  have h21 : localRange 5 (gtK 5).gmin 0 40612 = true := localRange_add' h20 gtK5_c21 rfl rfl
  have h22 : localRange 5 (gtK 5).gmin 0 42458 = true := localRange_add' h21 gtK5_c22 rfl rfl
  have h23 : localRange 5 (gtK 5).gmin 0 44304 = true := localRange_add' h22 gtK5_c23 rfl rfl
  have h24 : localRange 5 (gtK 5).gmin 0 46150 = true := localRange_add' h23 gtK5_c24 rfl rfl
  have h25 : localRange 5 (gtK 5).gmin 0 47996 = true := localRange_add' h24 gtK5_c25 rfl rfl
  have h26 : localRange 5 (gtK 5).gmin 0 49842 = true := localRange_add' h25 gtK5_c26 rfl rfl
  have h27 : localRange 5 (gtK 5).gmin 0 51688 = true := localRange_add' h26 gtK5_c27 rfl rfl
  have h28 : localRange 5 (gtK 5).gmin 0 53534 = true := localRange_add' h27 gtK5_c28 rfl rfl
  have h29 : localRange 5 (gtK 5).gmin 0 55380 = true := localRange_add' h28 gtK5_c29 rfl rfl
  have h30 : localRange 5 (gtK 5).gmin 0 57226 = true := localRange_add' h29 gtK5_c30 rfl rfl
  have h31 : localRange 5 (gtK 5).gmin 0 59049 = true := localRange_add' h30 gtK5_c31 rfl rfl
  intro idx hidx
  have hlen : (pairList 5).length = 10 := by decide
  have hidx' : idx < 59049 := by rw [hlen] at hidx; norm_num at hidx; exact hidx
  have := (localRange_iff 5 (gtK 5).gmin 0 59049).mp h31 idx hidx'
  rwa [Nat.zero_add] at this

theorem gtK_sound_five : GTabSound 5 (gtK 5) := gtabSound_of_local (by norm_num) (gtK 5) gtK_local_five

end BHH.E

namespace BHH

-- the deliverable of this file, also under `BHH` (helpers stay in `BHH.E`)
export E (gtK_sound_five)

end BHH
