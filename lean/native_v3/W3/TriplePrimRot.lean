/-
Window-3 entry primitives: `RotA3` and `ReflA3`.

* `rotA3`: the rotation `rotL φ` (W2's `GeoRot`) maps sectors to rotated sectors, preserves `A_3` (it preserves
  `sqDist` and commutes with negation and sums), and `(u, v, w) ↦ (R u, R v, R w)` preserves the product measure.
* `reflA3`: the same for the reflection `cnjL : (x, y) ↦ (x, -y)` (determinant `-1`), which maps the sector
  `(r1, r2, a, b)` onto the sector `(r1, r2, -b, -a)`.
Helper lemmas are in the namespace `BHH.W3.Prim`.
-/
import W3.Interfaces
import W2.TabRot

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W3

open BHH BHH.W2

namespace Prim

/-! ## Rotations -/

/-- a common rotation of the three arguments keeps `A_3` -/
lemma A3_rotL (φ : ℝ) (w' w z : Pt) : A3 (rotL φ w') (rotL φ w) (rotL φ z) = A3 w' w z := by
  unfold A3
  have hpre : rotL φ ⁻¹' (disk (rotL φ z) 1 \ (disk 0 1 ∪ disk (-rotL φ w) 1 ∪ disk (-rotL φ w - rotL φ w') 1)) =
      disk z 1 \ (disk 0 1 ∪ disk (-w) 1 ∪ disk (-w - w') 1) := by
    ext x
    have e0 : sqDist (rotL φ x) 0 = sqDist x 0 := by
      have := sqDist_rotL φ x 0
      rwa [map_zero] at this
    have e1 : sqDist (rotL φ x) (-rotL φ w) = sqDist x (-w) := by
      rw [show -rotL φ w = rotL φ (-w) from (map_neg _ _).symm, sqDist_rotL]
    have e2 : sqDist (rotL φ x) (-rotL φ w - rotL φ w') = sqDist x (-w - w') := by
      rw [show -rotL φ w - rotL φ w' = rotL φ (-w - w') by rw [map_sub, map_neg], sqDist_rotL]
    simp only [mem_preimage, mem_sdiff, mem_union, disk, mem_ofPred_eq, sqDist_rotL, e0, e1, e2]
  have hm : MeasurableSet (disk (rotL φ z) 1 \ (disk 0 1 ∪ disk (-rotL φ w) 1 ∪ disk (-rotL φ w - rotL φ w') 1)) :=
    (measurableSet_disk _ _).diff
      (((measurableSet_disk _ _).union (measurableSet_disk _ _)).union (measurableSet_disk _ _))
  rw [← hpre, (mp_rotL φ).measure_preimage hm.nullMeasurableSet]

end Prim

open Prim

/-- D3: rotating a triple of sectors keeps the integral of `A_3` (the angle conditions are not needed). -/
theorem rotA3 : RotA3 := by
  intro r1 r2 a b q1 q2 a' b' s1 s2 a'' b'' φ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  set T : Pt × (Pt × Pt) → Pt × (Pt × Pt) := fun p => (rotL φ p.1, (rotL φ p.2.1, rotL φ p.2.2)) with hT
  have hTmp : MeasurePreserving T volume volume := by
    have h := (mp_rotL φ).prod ((mp_rotL φ).prod (mp_rotL φ))
    rw [← Measure.volume_eq_prod (α := Pt) (β := Pt), ← Measure.volume_eq_prod (α := Pt) (β := Pt × Pt)] at h
    exact h
  have hTemb : MeasurableEmbedding T :=
    ((rotE φ).prodCongr ((rotE φ).prodCongr (rotE φ))).measurableEmbedding
  have himg : T '' (sector r1 r2 a b ×ˢ (sector q1 q2 a' b' ×ˢ sector s1 s2 a'' b'')) =
      sector r1 r2 (a + φ) (b + φ) ×ˢ (sector q1 q2 (a' + φ) (b' + φ) ×ˢ sector s1 s2 (a'' + φ) (b'' + φ)) := by
    rw [← rotL_image_sector φ r1 r2 a b, ← rotL_image_sector φ q1 q2 a' b', ← rotL_image_sector φ s1 s2 a'' b'',
      prod_image_image_eq, prod_image_image_eq]
  rw [← himg, hTmp.setIntegral_image_emb hTemb]
  simp only [hT, A3_rotL]

namespace Prim

/-! ## The reflection in the real axis -/

/-- the reflection `(x, y) ↦ (x, -y)`, as a linear map of `ℝ × ℝ` -/
def cnjL : Pt →ₗ[ℝ] Pt :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) !![1, 0; 0, -1]

lemma cnjL_apply (z : Pt) : cnjL z = (z.1, -z.2) := by
  rw [cnjL, Matrix.toLin_finTwoProd_apply]
  refine Prod.ext ?_ ?_ <;> simp

lemma det_cnjL : LinearMap.det cnjL = -1 := by
  rw [cnjL, LinearMap.det_toLin, Matrix.det_fin_two_of]
  norm_num

lemma sqDist_cnjL (a b : Pt) : sqDist (cnjL a) (cnjL b) = sqDist a b := by
  rw [cnjL_apply, cnjL_apply, sqDist, sqDist]
  simp only
  ring

lemma cnjL_cnjL (z : Pt) : cnjL (cnjL z) = z := by
  rw [cnjL_apply, cnjL_apply, neg_neg]

lemma mp_cnjL : MeasurePreserving cnjL volume volume := by
  have hne : LinearMap.det cnjL ≠ 0 := by rw [det_cnjL]; norm_num
  refine ⟨cnjL.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, det_cnjL]
  simp

/-- `cnjL` as a measurable equivalence -/
def cnjE : Pt ≃ᵐ Pt :=
  (LinearMap.equivOfDetNeZero cnjL (by rw [det_cnjL]; norm_num)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

lemma cnjE_coe : ⇑cnjE = cnjL := rfl

lemma cnjL_polar (ρ θ : ℝ) : cnjL (polarCoord.symm (ρ, θ)) = polarCoord.symm (ρ, -θ) := by
  rw [cnjL_apply, polarCoord_symm_apply, polarCoord_symm_apply, Real.cos_neg, Real.sin_neg]
  ext <;> simp

lemma cnjL_image_sector (r1 r2 a b : ℝ) : cnjL '' sector r1 r2 a b = sector r1 r2 (-b) (-a) := by
  ext x
  constructor
  · rintro ⟨_, ⟨⟨ρ, θ⟩, ⟨hρ, hθ⟩, rfl⟩, rfl⟩
    refine ⟨(ρ, -θ), ⟨hρ, ?_⟩, (cnjL_polar ρ θ).symm⟩
    simp only [mem_Ioo] at hθ ⊢
    constructor <;> linarith [hθ.1, hθ.2]
  · rintro ⟨⟨ρ, θ'⟩, ⟨hρ, hθ⟩, rfl⟩
    refine ⟨polarCoord.symm (ρ, -θ'), ⟨(ρ, -θ'), ⟨hρ, ?_⟩, rfl⟩, ?_⟩
    · simp only [mem_Ioo] at hθ ⊢
      constructor <;> linarith [hθ.1, hθ.2]
    · rw [cnjL_polar, neg_neg]

/-- the reflection keeps `A_3` -/
lemma A3_cnjL (w' w z : Pt) : A3 (cnjL w') (cnjL w) (cnjL z) = A3 w' w z := by
  unfold A3
  have hpre : cnjL ⁻¹' (disk (cnjL z) 1 \ (disk 0 1 ∪ disk (-cnjL w) 1 ∪ disk (-cnjL w - cnjL w') 1)) =
      disk z 1 \ (disk 0 1 ∪ disk (-w) 1 ∪ disk (-w - w') 1) := by
    ext x
    have e0 : sqDist (cnjL x) 0 = sqDist x 0 := by
      have := sqDist_cnjL x 0
      rwa [map_zero] at this
    have e1 : sqDist (cnjL x) (-cnjL w) = sqDist x (-w) := by
      rw [show -cnjL w = cnjL (-w) from (map_neg _ _).symm, sqDist_cnjL]
    have e2 : sqDist (cnjL x) (-cnjL w - cnjL w') = sqDist x (-w - w') := by
      rw [show -cnjL w - cnjL w' = cnjL (-w - w') by rw [map_sub, map_neg], sqDist_cnjL]
    simp only [mem_preimage, mem_sdiff, mem_union, disk, mem_ofPred_eq, sqDist_cnjL, e0, e1, e2]
  have hm : MeasurableSet (disk (cnjL z) 1 \ (disk 0 1 ∪ disk (-cnjL w) 1 ∪ disk (-cnjL w - cnjL w') 1)) :=
    (measurableSet_disk _ _).diff
      (((measurableSet_disk _ _).union (measurableSet_disk _ _)).union (measurableSet_disk _ _))
  rw [← hpre, mp_cnjL.measure_preimage hm.nullMeasurableSet]

end Prim

open Prim

/-- D4: reflecting a triple of sectors in the real axis keeps the integral of `A_3`, and maps the points of a sector
to the points of the reflected sector (the angle conditions are not needed). -/
theorem reflA3 : ReflA3 := by
  intro r1 r2 a b q1 q2 a' b' s1 s2 a'' b'' _ _ _ _ _ _ _ _ _
  refine ⟨?_, ?_⟩
  · set T : Pt × (Pt × Pt) → Pt × (Pt × Pt) := fun p => (cnjL p.1, (cnjL p.2.1, cnjL p.2.2)) with hT
    have hTmp : MeasurePreserving T volume volume := by
      have h := mp_cnjL.prod (mp_cnjL.prod mp_cnjL)
      rw [← Measure.volume_eq_prod (α := Pt) (β := Pt), ← Measure.volume_eq_prod (α := Pt) (β := Pt × Pt)] at h
      exact h
    have hTemb : MeasurableEmbedding T := (cnjE.prodCongr (cnjE.prodCongr cnjE)).measurableEmbedding
    have himg : T '' (sector r1 r2 a b ×ˢ (sector q1 q2 a' b' ×ˢ sector s1 s2 a'' b'')) =
        sector r1 r2 (-b) (-a) ×ˢ (sector q1 q2 (-b') (-a') ×ˢ sector s1 s2 (-b'') (-a'')) := by
      rw [← cnjL_image_sector r1 r2 a b, ← cnjL_image_sector q1 q2 a' b', ← cnjL_image_sector s1 s2 a'' b'',
        prod_image_image_eq, prod_image_image_eq]
    rw [← himg, hTmp.setIntegral_image_emb hTemb]
    simp only [hT, A3_cnjL]
  · intro z
    have hinj : Function.Injective cnjL := fun x y h => by
      rw [← cnjL_cnjL x, h, cnjL_cnjL]
    rw [← cnjL_apply z, ← cnjL_image_sector r1 r2 a b, hinj.mem_set_image]

end BHH.W3
