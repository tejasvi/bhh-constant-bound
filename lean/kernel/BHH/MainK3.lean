/-
The kernel-only proof, K3: `MainBoundsK3` from the K2 trees of `C_3` and `C_4` (leaf function `LkKf`) and the coarse kernel
tree of `C_5` (`5 0.6 0.0005 3e-10`, 2^22 initial boxes, leaf function `LkKt`), then `BetaBoundK3` and `BHHBetaBoundK3`.
The soundness of the k = 5 table `gtK 5` is `gtK_sound_five` (BHH/GraphK5.lean).
-/
import BHH.MainK
import BHH.BetaK3
import BHH.LeafSound.FinalKf
import BHH.LeafSound.FinalKt
import BHH.KSub2.K3.Asm
import BHH.KSub2.K4.Asm
import BHH.KSub3.K5.Asm
import BHH.GraphK5

namespace BHH

open BHH.Cert BHH.KC

/-- `MainBoundsK3`, given the soundness of the k = 5 table `gtK 5` -/
theorem mainBoundsK3_of_gt5 (hgt5 : GTabSound 5 (gtK 5)) : MainBoundsK3 := by
  intro hG hV
  have hp := BHH.E.piThreeHalvesLo_nonneg
  refine ⟨?_, ?_, ?_⟩
  · exact C_ge_of_rangeK (by norm_num) (BHH.KSub2.K3.range (leafSound_Kf_final hG hV 3 le_rfl (by norm_num)))
      (by positivity) kappa_three_gt.le (by norm_num [piThreeHalvesLo, BHH.KSub2.K3.S, BHH.Cert.OS])
  · exact C_ge_of_rangeK (by norm_num) (BHH.KSub2.K4.range (leafSound_Kf_final hG hV 4 (by norm_num) le_rfl))
      (by positivity) kappa_four_gt.le (by norm_num [piThreeHalvesLo, BHH.KSub2.K4.S, BHH.Cert.OS])
  · exact C_ge_of_rangeK (by norm_num) (BHH.KSub3.K5.range (leafSound_K5t_of hgt5 hG hV))
      (by positivity) kappa_five_gt.le (by norm_num [piThreeHalvesLo, BHH.KSub3.K5.S, BHH.Cert.OS])

theorem mainBoundsK3 : MainBoundsK3 := mainBoundsK3_of_gt5 gtK_sound_five

theorem betaBoundK3 : BetaBoundK3 := betaBoundK3_of mainBoundsK3

theorem bhhBetaBoundK3 : BHHBetaBoundK3 := bhhBetaBoundK3_of betaBoundK3

end BHH
