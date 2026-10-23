/-
Window-3 entries: `tripleSound : CosSinTSound → AsinTSound → TriRangeSound → TripleSound`.

For the triple entry `(ia, ib, ic, dab, dbc)` (cells `Z_a = (ia, 0)`, `Z_b = (ib, dab)`, `Z_c = (ic, dab + dbc)`):
* T class: `max |z_a + z_b + z_c| ≤ triRange28.2 ≤ 1` on the cells (`TriRangeSound`);
* `ā_3`: always `A_3(z_a, z_b, z_c) ≤ A_2(z_b, z_c)` pointwise, so the mean of `A_3` is at most `ā_2(Z_b, Z_c)` (rotation
  of the pair by `-dab`, W2's `rotA2`); this covers the far triples and the fallbacks; on the vertex path
  `A_3 = A_4 - A(-(z_a + z_b), -z_b, 0)` with the four-disk vertex lemma at the rounded centroids (`te_tri_core`, six
  pairs, the `(P0, P3)` range from `TriRangeSound` on the closed convex hulls) and the subtracted mean bounded below by
  the given `LV3LO`, hence `E A_3 ≤ min(ā_2, v) ≤ max(min(ā_2, v), 0)`.
-/
import W3.TripleEntryLV3
import W2.TabRot

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W3

open BHH BHH.W2 BHH.Cert W2C

/-- `tripleEntryF` with the destructuring `let`s replaced by projections (definitionally equal). -/
def te_triE (g : Grid) (ia ib ic : ℕ) (dab dbc : ℤ) (pbc pab : W3C.PairE) : W3C.TripE :=
  let td := W3C.mkTabData g
  let ch := td.ad.ch
  let Ra := td.rings[ia]!
  let Rb := td.rings[ib]!
  let Rc := td.rings[ic]!
  let Ga := W3C.geoAt g td.geo ia 0
  let Gb := W3C.geoAt g td.geo ib dab
  let Gc := W3C.geoAt g td.geo ic (dab + dbc)
  match W3C.triRange28 Ga.pv Gb.pv Gc.pv with
  | (mn, mx) =>
  let tcls := decide (mx ≤ ONE)
  let a2 := pbc.abar2
  if 2 * ONE ≤ mn then ⟨tcls, a2⟩
  else
    let px0 := Iv.add Ga.cx Gb.cx
    let py0 := Iv.add Ga.cy Gb.cy
    let p0x := -(ivMid px0)
    let p0y := -(ivMid py0)
    let p1x := -(ivMid Gb.cx)
    let p1y := -(ivMid Gb.cy)
    let p3x := ivMid Gc.cx
    let p3y := ivMid Gc.cy
    let ep0 := W3C.dist px0 py0 (-p0x) (-p0y)
    let ep1 := W3C.dist Gb.cx Gb.cy (-p1x) (-p1y)
    let ep3 := W3C.dist Gc.cx Gc.cy p3x p3y
    match BHH.Cert.unionArea (W3C.cosSinT td.cst) [(p0x, p0y), (p1x, p1y), (0, 0), (p3x, p3y)] ONE W3C.candF with
    | none => ⟨tcls, a2⟩
    | some ur =>
      let sq := [W3C.sqm Ra, W3C.sqm Rb, W3C.sqm Rc]
      match W3C.lvPairT td.atab (W3C.hullR Ra ch (ep0 + ep1 + 1)).1 (W3C.hullR Ra ch (ep0 + ep1 + 1)).2
          (W3C.momentsX [1, 2, 0] sq (ep0 + ep1)).1 (W3C.momentsX [1, 2, 0] sq (ep0 + ep1)).2,
        W3C.lvPairT td.atab (W3C.hsAt td ia ib dab (ep0 + 1)).1 (W3C.hsAt td ia ib dab (ep0 + 1)).2
          (W3C.momentsX [1, 1, 0] sq ep0).1 (W3C.momentsX [1, 1, 0] sq ep0).2,
        W3C.lvPairT td.atab (mn - (ep0 + ep3 + 1)) (mx + ep0 + ep3 + 1)
          (W3C.momentsX [1, 1, 1] sq (ep0 + ep3)).1 (W3C.momentsX [1, 1, 1] sq (ep0 + ep3)).2,
        W3C.lvPairT td.atab (W3C.hullR Rb ch (ep1 + 1)).1 (W3C.hullR Rb ch (ep1 + 1)).2
          (W3C.momentsX [0, 1, 0] sq ep1).1 (W3C.momentsX [0, 1, 0] sq ep1).2,
        W3C.lvPairT td.atab (W3C.hsAt td ib ic dbc (ep1 + ep3 + 1)).1 (W3C.hsAt td ib ic dbc (ep1 + ep3 + 1)).2
          (W3C.momentsX [0, 1, 1] sq (ep1 + ep3)).1 (W3C.momentsX [0, 1, 1] sq (ep1 + ep3)).2,
        W3C.lvPairT td.atab (W3C.hullR Rc ch (ep3 + 1)).1 (W3C.hullR Rc ch (ep3 + 1)).2
          (W3C.momentsX [0, 0, 1] sq ep3).1 (W3C.momentsX [0, 0, 1] sq ep3).2 with
      | some a, some b, some c, some d, some e, some f =>
        ⟨tcls, Max.max (Min.min a2 (ur.A.hi + 2 * (ep0 + ep1 + ep3) + (a + b + c + d + e + f) - pab.lv3 + 2)) 0⟩
      | _, _, _, _, _, _ => ⟨tcls, a2⟩

lemma te_tripleEntryF_eq (g : Grid) (ia ib ic : ℕ) (dab dbc : ℤ) (pbc pab : W3C.PairE) :
    W3C.tripleEntryF (W3C.mkTabData g) ia ib ic dab dbc pbc pab = te_triE g ia ib ic dab dbc pbc pab := by
  unfold W3C.tripleEntryF te_triE
  simp only [show (W3C.mkTabData g).g = g from rfl]
  generalize W3C.triRange28 (W3C.geoAt g (W3C.mkTabData g).geo ia 0).pv (W3C.geoAt g (W3C.mkTabData g).geo ib dab).pv
    (W3C.geoAt g (W3C.mkTabData g).geo ic (dab + dbc)).pv = T
  obtain ⟨mn, mx⟩ := T
  rfl


/-! ## The three-disk difference `A_3` -/

lemma te_iUnion_four (a b c d : Pt) :
    (⋃ i : Fin 4, disk (![a, b, c, d] i) 1) = disk a 1 ∪ disk b 1 ∪ disk c 1 ∪ disk d 1 := by
  ext x
  simp only [mem_iUnion, mem_union, Fin.exists_fin_succ, Fin.exists_fin_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, or_false, or_assoc]

/-- `A_3(z_a, z_b, z_c) = A(-(z_a + z_b), -z_b, 0, z_c) - A(-(z_a + z_b), -z_b, 0)` -/
lemma te_A3_eq (za zb zc : Pt) :
    A3 za zb zc = unionArea ![-(za + zb), -zb, (0 : Pt), zc] - unionArea ![-(za + zb), -zb, (0 : Pt)] := by
  unfold A3 unionArea
  have hm := measurableSet_disk
  have hf := tp_volume_disk_ne_top
  rw [te_iUnion_four, tp_iUnion_three]
  have hA : MeasurableSet (disk 0 1 ∪ disk (-zb) 1 ∪ disk (-zb - za) 1) := ((hm _ _).union (hm _ _)).union (hm _ _)
  have hAf : volume (disk 0 1 ∪ disk (-zb) 1 ∪ disk (-zb - za) 1) ≠ ⊤ :=
    measure_union_ne_top (measure_union_ne_top (hf _) (hf _)) (hf _)
  rw [tp_vol_diff_eq hA (hm _ _) hAf (hf _)]
  have e0 : -zb - za = -(za + zb) := by abel
  rw [e0]
  have e1 : disk 0 1 ∪ disk (-zb) 1 ∪ disk (-(za + zb)) 1 ∪ disk zc 1 =
      disk (-(za + zb)) 1 ∪ disk (-zb) 1 ∪ disk 0 1 ∪ disk zc 1 := by
    ext x; simp only [mem_union]; tauto
  have e2 : disk 0 1 ∪ disk (-zb) 1 ∪ disk (-(za + zb)) 1 = disk (-(za + zb)) 1 ∪ disk (-zb) 1 ∪ disk 0 1 := by
    ext x; simp only [mem_union]; tauto
  rw [e1, e2]

lemma te_A3_nonneg (za zb zc : Pt) : 0 ≤ A3 za zb zc := ENNReal.toReal_nonneg

/-- `A_3(z_a, z_b, z_c) ≤ A_2(z_b, z_c)` (one disk fewer is removed) -/
lemma te_A3_le_A2 (za zb zc : Pt) : A3 za zb zc ≤ A2 zb zc := by
  unfold A3 A2
  exact ENNReal.toReal_mono (measure_ne_top_of_subset sdiff_subset (tp_volume_disk_ne_top zc))
    (measure_mono (sdiff_subset_sdiff_right subset_union_left))

/-! ## Integrability on products of three cells -/

lemma te_volume_prod3_ne_top {A B C : Set Pt} (hA : volume A ≠ ⊤) (hB : volume B ≠ ⊤) (hC : volume C ≠ ⊤) :
    volume (A ×ˢ (B ×ˢ C)) ≠ ⊤ := by
  rw [Measure.volume_eq_prod (α := Pt) (β := Pt × Pt), Measure.prod_prod,
    Measure.volume_eq_prod (α := Pt) (β := Pt), Measure.prod_prod]
  exact ENNReal.mul_ne_top hA (ENNReal.mul_ne_top hB hC)

lemma te_integrableOn_bdd3 {s : Set (Pt × (Pt × Pt))} (hs : volume s ≠ ⊤) {f : Pt × (Pt × Pt) → ℝ}
    (hf : Measurable f) {M : ℝ} (hb : ∀ p, |f p| ≤ M) : IntegrableOn f s :=
  Measure.integrableOn_of_bounded (M := M) hs hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hb p)

lemma te_int3_A2 {A B C : Set Pt} (hA : volume A ≠ ⊤) (hB : volume B ≠ ⊤) (hC : volume C ≠ ⊤) :
    IntegrableOn (fun p : Pt × (Pt × Pt) => A2 p.2.1 p.2.2) (A ×ˢ (B ×ˢ C)) :=
  te_integrableOn_bdd3 (te_volume_prod3_ne_top hA hB hC) (measurable_A2.comp measurable_snd) (M := π) fun p => by
    rw [abs_of_nonneg (A2_nonneg _ _)]; exact A2_le_pi _ _

lemma te_int3_U3 {A B C : Set Pt} (hA : volume A ≠ ⊤) (hB : volume B ≠ ⊤) (hC : volume C ≠ ⊤) :
    IntegrableOn (fun p : Pt × (Pt × Pt) => unionArea ![-(p.1 + p.2.1), -p.2.1, (0 : Pt)]) (A ×ˢ (B ×ˢ C)) := by
  have e : (fun p : Pt × (Pt × Pt) => unionArea ![-(p.1 + p.2.1), -p.2.1, (0 : Pt)]) =
      fun p => A2 p.1 p.2.1 + π + A1 p.1 := funext fun p => te_unionArea_lv3 p.1 p.2.1
  rw [e]
  have hmeas : Measurable fun p : Pt × (Pt × Pt) => A2 p.1 p.2.1 + π + A1 p.1 :=
    ((measurable_A2.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).add measurable_const).add
      (measurable_A1.comp measurable_fst)
  refine te_integrableOn_bdd3 (te_volume_prod3_ne_top hA hB hC) hmeas (M := 3 * π) fun p => ?_
  have h1 := A2_nonneg p.1 p.2.1
  have h2 := A2_le_pi p.1 p.2.1
  have h3 := A1_nonneg p.1
  have h4 := A1_le_pi p.1
  rw [abs_of_nonneg (by linarith [Real.pi_pos])]
  linarith

/-! ## Rotation of the `A_2` integral and of the cell areas -/

section Rot

variable {g : Grid}

lemma te_rot_A2 (hg : GridOK g) {ib ic : ℕ} {dab dbc : ℤ} (hab : |dab| < g.NT) (hbc : |dbc| < g.NT)
    (habc : |dab + dbc| < g.NT) :
    ∫ p in rcell g ib dab ×ˢ rcell g ic (dab + dbc), A2 p.1 p.2 =
      ∫ p in rcell g ib 0 ×ˢ rcell g ic dbc, A2 p.1 p.2 := by
  have hb := te_secOK hg ib hab
  have hc := te_secOK hg ic habc
  have hb0 := te_secOK hg ib (show |(0 : ℤ)| < g.NT by simp only [abs_zero, Nat.cast_pos]; have := hg.2.2.1; omega)
  have hc0 := te_secOK hg ic hbc
  have h := rotA2 ((gR g).rad ib) ((gR g).rad (ib + 1)) (dab * (π / g.NT)) ((dab + 1) * (π / g.NT))
    ((gR g).rad ic) ((gR g).rad (ic + 1)) (((dab + dbc : ℤ) : ℝ) * (π / g.NT)) ((((dab + dbc : ℤ) : ℝ) + 1) * (π / g.NT))
    (-(dab * (π / g.NT))) hb.1 hc.1 hb.2.2.1 hb.2.2.2.2.1 hc.2.2.1 hc.2.2.2.2.1
    (by have := hb0.2.2.1; push_cast at this ⊢; linarith) (by have := hb0.2.2.2.2.1; push_cast at this ⊢; linarith)
    (by have := hc0.2.2.1; push_cast at this ⊢; linarith) (by have := hc0.2.2.2.2.1; push_cast at this ⊢; linarith)
  rw [te_rcell_eq, te_rcell_eq, h, te_rcell_eq, te_rcell_eq]
  congr 3 <;> push_cast <;> ring

lemma te_vr_shift (hg : GridOK g) (ib : ℕ) {j : ℤ} (hj : |j| < g.NT) : vr g ib j = vr g ib 0 := by
  have h0 : |(0 : ℤ)| < g.NT := by simp only [abs_zero, Nat.cast_pos]; have := hg.2.2.1; omega
  rw [te_vr_eq, te_vr_eq, te_rcell_eq, te_rcell_eq, volume_sector_toReal (te_secOK hg ib hj),
    volume_sector_toReal (te_secOK hg ib h0)]
  push_cast; ring

end Rot


lemma te_ptsCfg4 (a b c d e f : ℤ) :
    ptsCfg 4 [(a, b), (c, d), (0, 0), (e, f)] = ![(fx a, fx b), (fx c, fx d), (0 : Pt), (fx e, fx f)] := by
  funext i; fin_cases i <;> simp [ptsCfg, fx]

set_option maxHeartbeats 8000000 in
/-- D2 (`TripleSound`): the T class and the bound `ā_3` of the triple entries. -/
theorem tripleSound (hCS : CosSinTSound) (hAS : AsinTSound) (hTR : TriRangeSound) : TripleSound := by
  intro hG hV g hg ia ib ic dab dbc pbc pab hia hib hic hab hbc habc hpbc hpab
  have hNT := hg.2.2.1
  have h0 : |(0 : ℤ)| < g.NT := by simp only [abs_zero, Nat.cast_pos]; omega
  have hN0 : (0 : ℤ) ≤ (g.NT : ℤ) := Int.natCast_nonneg _
  have h0' : |(0 : ℤ)| ≤ 2 * (g.NT : ℤ) := by simp only [abs_zero]; positivity
  have hab' : |dab| ≤ 2 * (g.NT : ℤ) := by linarith
  have habc' : |dab + dbc| ≤ 2 * (g.NT : ℤ) := by linarith
  have hAm := te_rcell_meas hg ia h0
  have hBm := te_rcell_meas hg ib hab
  have hCm := te_rcell_meas hg ic habc
  have hA0 := te_rcell_ne0 hg ia h0
  have hB0 := te_rcell_ne0 hg ib hab
  have hC0 := te_rcell_ne0 hg ic habc
  have hAt := te_rcell_netop hg ia h0
  have hBt := te_rcell_netop hg ib hab
  have hCt := te_rcell_netop hg ic habc
  have hAb := te_rcell_bdd hg ia h0
  have hBb := te_rcell_bdd hg ib hab
  have hCb := te_rcell_bdd hg ic habc
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Pt × (Pt × Pt))) := by
    rw [Measure.volume_eq_prod (α := Pt) (β := Pt × Pt)]
    have : IsFiniteMeasureOnCompacts (volume : Measure (Pt × Pt)) := inferInstance
    infer_instance
  have hint : ∀ f : Pt × (Pt × Pt) → ℝ, Continuous f →
      IntegrableOn f (rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc))) :=
    fun f hf => tp_integrableOn_of_bounded (hAb.prod (hBb.prod hCb)) hf
  have hAi : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f (rcell g ia 0) :=
    fun f hf => tp_integrableOn_of_bounded hAb hf
  have hBi : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f (rcell g ib dab) :=
    fun f hf => tp_integrableOn_of_bounded hBb hf
  have hCi : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f (rcell g ic (dab + dbc)) :=
    fun f hf => tp_integrableOn_of_bounded hCb hf
  have hVa := te_vr_pos hg ia h0
  have hVb := te_vr_pos hg ib hab
  have hVc := te_vr_pos hg ic habc
  have hSm : MeasurableSet (rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc))) := hAm.prod (hBm.prod hCm)
  -- the bound by `ā_2(Z_b, Z_c)` (`A_3 ≤ A_2(z_b, z_c)`, rotation by `-dab`)
  have hA2b : ∫ p in rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), A3 p.1 p.2.1 p.2.2 ≤
      fx pbc.abar2 * vr g ia 0 * vr g ib dab * vr g ic (dab + dbc) := by
    have h1 : ∫ p in rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), A3 p.1 p.2.1 p.2.2 ≤
        ∫ p in rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), A2 p.2.1 p.2.2 :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => te_A3_nonneg _ _ _)
        (te_int3_A2 hAt hBt hCt) (Filter.Eventually.of_forall fun p => te_A3_le_A2 _ _ _)
    rw [te_int3_snd (fun q => A2 q.1 q.2), te_rot_A2 hg hab hbc habc] at h1
    have hvb := te_vr_shift hg ib hab
    have hvc := te_vr_shift hg ic habc
    have hvc' := te_vr_shift hg ic hbc
    rw [te_vr_eq] at hpbc
    have hA := mul_le_mul_of_nonneg_left hpbc hVa.le
    rw [te_vr_eq] at hVa
    rw [hvb, hvc, ← hvc', te_vr_eq ia 0]
    rw [te_vr_eq] at hvb hvc hvc'
    calc ∫ p in rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), A3 p.1 p.2.1 p.2.2
        ≤ (volume (rcell g ia 0)).toReal * ∫ q in rcell g ib 0 ×ˢ rcell g ic dbc, A2 q.1 q.2 := h1
      _ ≤ (volume (rcell g ia 0)).toReal * (fx pbc.abar2 * vr g ib 0 * vr g ic dbc) := by
          rw [te_vr_eq ib 0, te_vr_eq ic dbc]; exact hA
      _ = _ := by ring
  -- the code
  rw [te_tripleEntryF_eq]
  unfold te_triE
  simp only [show (W3C.mkTabData g).atab = W3C.mkAsinTab from rfl, show (W3C.mkTabData g).cst = W3C.mkCsTab from rfl,
    show (W3C.mkTabData g).ad = mkAData g from rfl, te_rings g hia, te_rings g hib, te_rings g hic]
  generalize hT : W3C.triRange28 (W3C.geoAt g (W3C.mkTabData g).geo ia 0).pv
    (W3C.geoAt g (W3C.mkTabData g).geo ib dab).pv (W3C.geoAt g (W3C.mkTabData g).geo ic (dab + dbc)).pv = T
  obtain ⟨mn, mx⟩ := T
  dsimp only
  simp only [te_geoAt g hia h0', te_geoAt g hib hab', te_geoAt g hic habc']
  -- the T class
  have hTc : decide (mx ≤ ONE) = true → ∀ u ∈ rcell g ia 0, ∀ v ∈ rcell g ib dab, ∀ w ∈ rcell g ic (dab + dbc),
      sqDist (u + v + w) 0 ≤ 1 := by
    intro h u hu v hv w hw
    have hm : mx ≤ ONE := of_decide_eq_true h
    obtain ⟨-, h2⟩ := hTR g hg ia ib ic dab dbc hia hib hic hab hbc habc u
      (subset_closure (subset_convexHull ℝ _ hu)) v (subset_closure (subset_convexHull ℝ _ hv)) w
      (subset_closure (subset_convexHull ℝ _ hw))
    rw [hT] at h2
    have h1 : fx mx ≤ 1 := by have := te_fx_mono hm; rwa [te_fx_ONE] at this
    rw [sqDist_add_zero]
    have hn := enorm2_nonneg (u + v + w)
    nlinarith
  split_ifs with hfar
  · exact ⟨hTc, hA2b⟩
  · split
    · exact ⟨hTc, hA2b⟩
    · next ur hur =>
      split
      · next a b c d e f h01 h02 h03 h12 h13 h23 =>
        refine ⟨hTc, ?_⟩
        set Ga := W3C.mkGeo g (mkRing g ia) (mkAData g).ch 0 with hGa
        set Gb := W3C.mkGeo g (mkRing g ib) (mkAData g).ch dab with hGb
        set Gc := W3C.mkGeo g (mkRing g ic) (mkAData g).ch (dab + dbc) with hGc
        set px0 := Ga.cx.add Gb.cx with hpx0
        set py0 := Ga.cy.add Gb.cy with hpy0
        set p0x := -ivMid px0 with hp0x
        set p0y := -ivMid py0 with hp0y
        set p1x := -ivMid Gb.cx with hp1x
        set p1y := -ivMid Gb.cy with hp1y
        set p3x := ivMid Gc.cx with hp3x
        set p3y := ivMid Gc.cy with hp3y
        set ep0 := W3C.dist px0 py0 (-p0x) (-p0y) with hep0
        set ep1 := W3C.dist Gb.cx Gb.cy (-p1x) (-p1y) with hep1
        set ep3 := W3C.dist Gc.cx Gc.cy p3x p3y with hep3
        set c0 : Pt := (fx p0x, fx p0y) with hc0
        set c1 : Pt := (fx p1x, fx p1y) with hc1
        set c3 : Pt := (fx p3x, fx p3y) with hc3
        set Ca := cen (rcell g ia 0) with hCa
        set Cb := cen (rcell g ib dab) with hCb
        set Cc := cen (rcell g ic (dab + dbc)) with hCc
        obtain ⟨hCa1, hCa2⟩ := te_cen_mem hg hia h0
        obtain ⟨hCb1, hCb2⟩ := te_cen_mem hg hib hab
        obtain ⟨hCc1, hCc2⟩ := te_cen_mem hg hic habc
        -- the centroid errors
        have he0 : edist2 (Ca + Cb) (-c0) ≤ fx ep0 := by
          have h := TabB.distSound.1 px0 py0 (-p0x) (-p0y) (Ca + Cb).1 (Ca + Cb).2 (Iv.mem_add hCa1 hCb1)
            (Iv.mem_add hCa2 hCb2)
          have e2 : ((fx (-p0x), fx (-p0y)) : Pt) = -c0 := by
            rw [hc0, te_fx_neg p0x, te_fx_neg p0y]; rfl
          rw [e2] at h; exact h
        have he1 : edist2 Cb (-c1) ≤ fx ep1 := by
          have h := TabB.distSound.1 Gb.cx Gb.cy (-p1x) (-p1y) Cb.1 Cb.2 hCb1 hCb2
          have e2 : ((fx (-p1x), fx (-p1y)) : Pt) = -c1 := by
            rw [hc1, te_fx_neg p1x, te_fx_neg p1y]; rfl
          rw [e2] at h; exact h
        have he3 : edist2 Cc c3 ≤ fx ep3 := TabB.distSound.1 Gc.cx Gc.cy p3x p3y Cc.1 Cc.2 hCc1 hCc2
        -- the union area at the expansion point
        have hU : unionArea ![c0, c1, (0 : Pt), c3] ≤ fx ur.A.hi := by
          have h := (unionSound hG (W3C.cosSinT W3C.mkCsTab) hCS W3C.candF 4 _ ur rfl hur).1
          rw [te_ptsCfg4] at h
          exact ivMem_hi_le h
        -- the segments
        have hs01 : ∀ p ∈ rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), ∀ t ∈ Icc (0 : ℝ) 1,
            fx (W3C.hullR (mkRing g ia) (mkAData g).ch (ep0 + ep1 + 1)).1 ≤
              enorm2 ((c1 - c0) + t • (p.1 - (c1 - c0))) ∧
            enorm2 ((c1 - c0) + t • (p.1 - (c1 - c0))) ≤
              fx (W3C.hullR (mkRing g ia) (mkAData g).ch (ep0 + ep1 + 1)).2 := by
          intro p hp t ht
          have hm : edist2 Ca (c1 - c0) ≤ fx ep0 + fx ep1 := by
            have e : Ca - (c1 - c0) = (Ca + Cb - -c0) + -(Cb - -c1) := by abel
            rw [← te_enorm2_sub_eq, e]
            refine (te_enorm2_add_le _ _).trans ?_
            rw [te_enorm2_neg, te_enorm2_sub_eq, te_enorm2_sub_eq]
            linarith
          exact te_seg_hullR hg hia h0 hm (E := ep0 + ep1) (by rw [te_fx_add]) p.1 hp.1 t ht
        have hs02 : ∀ p ∈ rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), ∀ t ∈ Icc (0 : ℝ) 1,
            fx (W3C.hsAt (W3C.mkTabData g) ia ib dab (ep0 + 1)).1 ≤ enorm2 (-c0 + t • ((p.1 + p.2.1) - -c0)) ∧
            enorm2 (-c0 + t • ((p.1 + p.2.1) - -c0)) ≤ fx (W3C.hsAt (W3C.mkTabData g) ia ib dab (ep0 + 1)).2 := by
          intro p hp t ht
          have hm : edist2 Ca (-c0 - Cb) ≤ fx ep0 := by
            rw [← te_enorm2_sub_eq, show Ca - (-c0 - Cb) = Ca + Cb - -c0 by abel, te_enorm2_sub_eq]; exact he0
          have h0d : |(0 : ℤ) + dab| < g.NT := by rwa [zero_add]
          have h := te_seg_hs hg hia hib h0 hab h0d hm (E := ep0) le_rfl p.1 hp.1 p.2.1
            (by rw [zero_add]; exact hp.2.1) t ht
          have e : (-c0 - Cb + t • (p.1 - (-c0 - Cb))) + (cen (rcell g ib (0 + dab)) +
              t • (p.2.1 - cen (rcell g ib (0 + dab)))) = -c0 + t • ((p.1 + p.2.1) - -c0) := by
            rw [zero_add]; ext <;> simp <;> ring
          rw [e] at h; exact h
        have hs03 : ∀ p ∈ rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), ∀ t ∈ Icc (0 : ℝ) 1,
            fx (mn - (ep0 + ep3 + 1)) ≤ enorm2 ((c3 - c0) + t • ((p.2.2 + (p.1 + p.2.1)) - (c3 - c0))) ∧
            enorm2 ((c3 - c0) + t • ((p.2.2 + (p.1 + p.2.1)) - (c3 - c0))) ≤ fx (mx + ep0 + ep3 + 1) := by
          intro p hp t ht
          have hm : edist2 (Ca + Cb + Cc) (c3 - c0) ≤ fx ep0 + fx ep3 := by
            have e : Ca + Cb + Cc - (c3 - c0) = (Ca + Cb - -c0) + (Cc - c3) := by abel
            rw [← te_enorm2_sub_eq, e]
            refine (te_enorm2_add_le _ _).trans ?_
            rw [te_enorm2_sub_eq, te_enorm2_sub_eq]
            linarith
          have h := te_seg_tri hg hTR hia hib hic hab hbc habc hm p.1 hp.1 p.2.1 hp.2.1 p.2.2 hp.2.2 t ht
          rw [hT] at h
          simp only [te_fx_sub, te_fx_add]
          obtain ⟨h1, h2⟩ := h
          constructor <;> linarith [te_fx_one_pos]
        have hs12 : ∀ p ∈ rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), ∀ t ∈ Icc (0 : ℝ) 1,
            fx (W3C.hullR (mkRing g ib) (mkAData g).ch (ep1 + 1)).1 ≤ enorm2 (-c1 + t • (p.2.1 - -c1)) ∧
            enorm2 (-c1 + t • (p.2.1 - -c1)) ≤ fx (W3C.hullR (mkRing g ib) (mkAData g).ch (ep1 + 1)).2 := by
          intro p hp t ht
          exact te_seg_hullR hg hib hab he1 (E := ep1) le_rfl p.2.1 hp.2.1 t ht
        have hs13 : ∀ p ∈ rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), ∀ t ∈ Icc (0 : ℝ) 1,
            fx (W3C.hsAt (W3C.mkTabData g) ib ic dbc (ep1 + ep3 + 1)).1 ≤
              enorm2 ((c3 - c1) + t • ((p.2.2 + p.2.1) - (c3 - c1))) ∧
            enorm2 ((c3 - c1) + t • ((p.2.2 + p.2.1) - (c3 - c1))) ≤
              fx (W3C.hsAt (W3C.mkTabData g) ib ic dbc (ep1 + ep3 + 1)).2 := by
          intro p hp t ht
          have hm : edist2 Cb ((c3 - c1) - Cc) ≤ fx ep1 + fx ep3 := by
            have e : Cb - ((c3 - c1) - Cc) = (Cb - -c1) + (Cc - c3) := by abel
            rw [← te_enorm2_sub_eq, e]
            refine (te_enorm2_add_le _ _).trans ?_
            rw [te_enorm2_sub_eq, te_enorm2_sub_eq]
            linarith
          have h := te_seg_hs hg hib hic hab hbc habc hm (E := ep1 + ep3) (by rw [te_fx_add]) p.2.1 hp.2.1 p.2.2
            hp.2.2 t ht
          have e : ((c3 - c1) - Cc + t • (p.2.1 - ((c3 - c1) - Cc))) + (Cc + t • (p.2.2 - Cc)) =
              (c3 - c1) + t • ((p.2.2 + p.2.1) - (c3 - c1)) := by
            ext <;> simp <;> ring
          rw [e] at h; exact h
        have hs23 : ∀ p ∈ rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), ∀ t ∈ Icc (0 : ℝ) 1,
            fx (W3C.hullR (mkRing g ic) (mkAData g).ch (ep3 + 1)).1 ≤ enorm2 (c3 + t • (p.2.2 - c3)) ∧
            enorm2 (c3 + t • (p.2.2 - c3)) ≤ fx (W3C.hullR (mkRing g ic) (mkAData g).ch (ep3 + 1)).2 := by
          intro p hp t ht
          exact te_seg_hullR hg hic habc he3 (E := ep3) le_rfl p.2.2 hp.2.2 t ht
        -- the subtracted three-disk area
        have hHi := te_int3_U3 hAt hBt hCt
        have hH : fx pab.lv3 * ((volume (rcell g ia 0)).toReal * (volume (rcell g ib dab)).toReal *
            (volume (rcell g ic (dab + dbc))).toReal) ≤
            ∫ p in rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)),
              unionArea ![-(p.1 + p.2.1), -p.2.1, (0 : Pt)] := by
          have e := te_int3_fst12 (A := rcell g ia 0) (B := rcell g ib dab) (C := rcell g ic (dab + dbc))
            (fun q : Pt × Pt => unionArea ![-(q.1 + q.2), -q.2, (0 : Pt)])
          simp only at e
          rw [e]
          rw [te_vr_eq, te_vr_eq] at hpab
          rw [te_vr_eq] at hVc
          have := mul_le_mul_of_nonneg_right hpab hVc.le
          linarith
        have hcore := te_tri_core hV hAS hAm hBm hCm hint hAi hBi hCi hA0 hAt hB0 hBt hC0 hCt
          (te_momHi_nonneg g ia) (te_momHi_nonneg g ib) (te_momHi_nonneg g ic)
          (te_mom hg hia h0) (te_mom hg hib hab) (te_mom hg hic habc)
          (sqrt_pt_hi _) (sqrt_pt_hi _) (sqrt_pt_hi _) he0 he1 he3 hU h01 h02 h03 h12 h13 h23
          hs01 hs02 hs03 hs12 hs13 hs23 (F := fun p => A3 p.1 p.2.1 p.2.2)
          (H := fun p => unionArea ![-(p.1 + p.2.1), -p.2.1, (0 : Pt)]) (L := fx pab.lv3)
          (fun p => te_A3_nonneg _ _ _) (fun p _ => le_of_eq (te_A3_eq _ _ _)) hHi hH
        -- conclusion: `ā_3 = max(min(ā_2, v), 0)`
        rw [te_vr_eq] at hVa hVb hVc
        rw [te_vr_eq, te_vr_eq, te_vr_eq] at hA2b
        rw [te_vr_eq, te_vr_eq, te_vr_eq]
        have hv : (fx ur.A.hi + 2 * (fx ep0 + fx ep1 + fx ep3) +
            (fx a + fx b + fx c + fx d + fx e + fx f) - fx pab.lv3) ≤
            fx (ur.A.hi + 2 * (ep0 + ep1 + ep3) + (a + b + c + d + e + f) - pab.lv3 + 2) := by
          simp only [te_fx_sub, te_fx_add, te_fx_mul_two]
          have : (0 : ℝ) ≤ fx 2 := by unfold fx; positivity
          linarith
        have hVV : 0 < (volume (rcell g ia 0)).toReal * (volume (rcell g ib dab)).toReal *
            (volume (rcell g ic (dab + dbc))).toReal := by positivity
        have h1 := mul_le_mul_of_nonneg_right hv hVV.le
        have hvb : ∫ p in rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), A3 p.1 p.2.1 p.2.2 ≤
            fx (ur.A.hi + 2 * (ep0 + ep1 + ep3) + (a + b + c + d + e + f) - pab.lv3 + 2) *
              ((volume (rcell g ia 0)).toReal * (volume (rcell g ib dab)).toReal *
                (volume (rcell g ic (dab + dbc))).toReal) := by
          linarith
        rw [te_fx_max, te_fx_min, te_fx_zero]
        set W := (volume (rcell g ia 0)).toReal * (volume (rcell g ib dab)).toReal *
          (volume (rcell g ic (dab + dbc))).toReal with hW
        have hA2b' : ∫ p in rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), A3 p.1 p.2.1 p.2.2 ≤
            fx pbc.abar2 * W := hA2b.trans (le_of_eq (by rw [hW]; ring))
        calc ∫ p in rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), A3 p.1 p.2.1 p.2.2
            ≤ min (fx pbc.abar2) (fx (ur.A.hi + 2 * (ep0 + ep1 + ep3) + (a + b + c + d + e + f) - pab.lv3 + 2)) *
              W := by
              rw [min_mul_of_nonneg _ _ hVV.le]; exact le_min hA2b' hvb
          _ ≤ max (min (fx pbc.abar2)
                (fx (ur.A.hi + 2 * (ep0 + ep1 + ep3) + (a + b + c + d + e + f) - pab.lv3 + 2))) 0 * W :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hVV.le
          _ = _ := by rw [hW]; ring
      · exact ⟨hTc, hA2b⟩

end BHH.W3
