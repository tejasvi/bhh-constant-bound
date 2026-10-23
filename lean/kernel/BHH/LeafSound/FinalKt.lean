/-
Module D for the kernel-only proof with the literal-table cos/sin and the fast untrusted candidates: leaf soundness of `LkKt k`
(k = 3, 4; and k = 5 given the soundness of the table `gtK 5`). The proofs are those of `leafSound_K_final`
(BHH/LeafSound/FinalK.lean) and `leafSound_K5_of` (the case k = 5) with `cosSinTabLit` / `cosSinTabLit_sound`
(BHH/TrigTabLit.lean) and `fastCand` / `fastAsin` as arguments of `leafSound_top` and `D38.prop38Spec_of`; standard
axioms only.
-/
import BHH.LeafSound.FinalK
import BHH.TrigTabLit
import BHHCert.ShardKt

open BHH.Cert

noncomputable section

namespace BHH

/-- Module D, kernel-only proof, literal-table cos/sin and fast candidates: leaf soundness of `LkKt k` for k = 3, 4. -/
theorem leafSound_Kt_final :
    GreenFormula → VertexLemmaSeg → ∀ k : ℕ, 3 ≤ k → k ≤ 4 → LeafSoundProp k (LkKt k) := by
  intro hG hVL k hk3 hk4
  have hgt := gtK_sound_k hk3 hk4
  exact leafSound_top hk3 (by omega) hgt cosSinTabLit_sound fastCand fastAsin (fun idx _ => gtK_nonneg_D k idx) hG hVL
    unionSound bracketProp remMaxProp remMomentsProp unionAreaGePiProp
    (D38.prop38Spec_of hk3 hgt cosSinTabLit_sound fastCand hG unionSoundR enlargedDisksProp unionAreaGePiProp)
    (straddleSpec_of hk3 hgt eventBoundProp straddleProp)
    (DX.extraSpec_of hk3 hgt eventBoundProp partitionBoundProp probStripsProp edgeIndepProp)

/-- leaf soundness of `LkKt 5`, from the soundness of the table `gtK 5` -/
theorem leafSound_K5t_of (hgt5 : GTabSound 5 (gtK 5)) :
    GreenFormula → VertexLemmaSeg → LeafSoundProp 5 (LkKt 5) := fun hG hVL =>
  leafSound_top (by norm_num) (le_refl 5) hgt5 cosSinTabLit_sound fastCand fastAsin (fun idx _ => gtK_nonneg_D 5 idx)
    hG hVL unionSound bracketProp remMaxProp remMomentsProp unionAreaGePiProp
    (D38.prop38Spec_of (by norm_num) hgt5 cosSinTabLit_sound fastCand hG unionSoundR enlargedDisksProp unionAreaGePiProp)
    (straddleSpec_of (by norm_num) hgt5 eventBoundProp straddleProp)
    (DX.extraSpec_of (by norm_num) hgt5 eventBoundProp partitionBoundProp probStripsProp edgeIndepProp)

end BHH
