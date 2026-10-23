/-
Window-3 entries: geometry of the relative cells for the window-3 entries.

* the relative cells `rcell g ir j` (`|j| < NT`) are admissible sectors; their centroids lie in the code's centroid
  intervals (`mkGeo`), their second moments are at most `momHi`, their hull radii are enclosed (T1, T2, T8 of W2);
* distance ranges along the segments from points near the centroids: `|z|` (`hullR`), `|z + z'|` (`hsAt`: the polar-box
  bound on the hulls, rotated by the angular offset of the first cell), `|z_a + z_b + z_c|` (`TriRangeSound` on the
  closed convex hulls; the centroid lies in the closed convex hull);
* the union area of `(-(z + z'), -z', 0)` (`= A_2(z, z') + π + A_1(z)` and `≥ π + A_1(z')`).
-/
import W3.TripleEntryCore
import W2.EntrySound
import W2.TabT14
import W2.TabCen
import W2.TabA

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W3

open BHH BHH.W2 BHH.Cert W2C

/-! ## The relative cells -/

section Cells

variable {g : Grid}

lemma te_gridOK_ring (hg : GridOK g) {j : ℕ} (hj : j < g.NR) :
    0 < (Iv.sub (Iv.sqr (radIv g (j + 1))) (Iv.sqr (radIv g j))).lo ∧ 0 < (Iv.div2e (dthIv g) 1).lo := by
  have h := hg.2.2.2.2.2.1 j hj
  simp only [ringOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

lemma te_ring (hg : GridOK g) {ir : ℕ} (hir : ir < g.NR) :
    ivMem ((gR g).rad ir) (mkRing g ir).r1 ∧ ivMem ((gR g).rad (ir + 1)) (mkRing g ir).r2 ∧
    fx (mkRing g ir).areaLo ≤ ((gR g).rad (ir + 1) ^ 2 - (gR g).rad ir ^ 2) * (π / g.NT) / 2 ∧
    ivMem (secRho ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT)) (mkRing g ir).rhoc ∧
    ((gR g).rad ir ^ 2 + (gR g).rad (ir + 1) ^ 2) / 2 - secRho ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT) ^ 2
      ≤ fx (mkRing g ir).momHi ∧
    fx (mkRing g ir).euLo ≤ meanA1 ((gR g).rad ir) ((gR g).rad (ir + 1)) ∧
    meanA1 ((gR g).rad ir) ((gR g).rad (ir + 1)) ≤ fx (mkRing g ir).euHi ∧
    ((mkRing g ir).nflag = true → (gR g).rad (ir + 1) ≤ 1) :=
  TabB.ringSound g hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.2.1 ir hir (te_gridOK_ring hg hir).1 (te_gridOK_ring hg hir).2

lemma te_secOK (hg : GridOK g) (ir : ℕ) {j : ℤ} (hj : |j| < g.NT) :
    SecOK ((gR g).rad ir) ((gR g).rad (ir + 1)) (j * (π / g.NT)) ((j + 1) * (π / g.NT)) :=
  secOK_z' g hg.1 hg.2.1 hg.2.2.1 ir hj

lemma te_rcell_eq (ir : ℕ) (j : ℤ) :
    rcell g ir j = sector ((gR g).rad ir) ((gR g).rad (ir + 1)) (j * (π / g.NT)) ((j + 1) * (π / g.NT)) := rfl

lemma te_vr_eq (ir : ℕ) (j : ℤ) : vr g ir j = (volume (rcell g ir j)).toReal := rfl

lemma te_rcell_meas (hg : GridOK g) (ir : ℕ) {j : ℤ} (hj : |j| < g.NT) : MeasurableSet (rcell g ir j) :=
  measurableSet_sector (te_secOK hg ir hj)

lemma te_rcell_ne0 (hg : GridOK g) (ir : ℕ) {j : ℤ} (hj : |j| < g.NT) : volume (rcell g ir j) ≠ 0 :=
  sector_ne_zero (te_secOK hg ir hj)

lemma te_rcell_netop (hg : GridOK g) (ir : ℕ) {j : ℤ} (hj : |j| < g.NT) : volume (rcell g ir j) ≠ ⊤ :=
  sector_ne_top (te_secOK hg ir hj)

lemma te_rcell_bdd (hg : GridOK g) (ir : ℕ) {j : ℤ} (hj : |j| < g.NT) : Bornology.IsBounded (rcell g ir j) :=
  sector_bounded (te_secOK hg ir hj).1

lemma te_vr_pos (hg : GridOK g) (ir : ℕ) {j : ℤ} (hj : |j| < g.NT) : 0 < vr g ir j :=
  volume_sector_pos (te_secOK hg ir hj)

lemma te_cen_rcell (hg : GridOK g) (ir : ℕ) {j : ℤ} (hj : |j| < g.NT) :
    cen (rcell g ir j) = secCentroid ((gR g).rad ir) ((gR g).rad (ir + 1)) (j * (π / g.NT)) ((j + 1) * (π / g.NT)) :=
  (sectorCen _ _ _ _ (te_secOK hg ir hj)).1

lemma te_mkDData_cx (g : Grid) (d : ℤ) :
    (mkDData g d).cx = cosIvG (Iv.div2e (Iv.mul (dthIv g) (Iv.int (2 * d + 1))) 1) := rfl
lemma te_mkDData_sy (g : Grid) (d : ℤ) :
    (mkDData g d).sy = sinIvG (Iv.div2e (Iv.mul (dthIv g) (Iv.int (2 * d + 1))) 1) := rfl

/-- the centroid of a relative cell lies in the code's centroid intervals -/
lemma te_cen_mem (hg : GridOK g) {ir : ℕ} (hir : ir < g.NR) {j : ℤ} (hj : |j| < g.NT) :
    ivMem (cen (rcell g ir j)).1 (W3C.mkGeo g (mkRing g ir) (mkAData g).ch j).cx ∧
    ivMem (cen (rcell g ir j)).2 (W3C.mkGeo g (mkRing g ir) (mkAData g).ch j).cy := by
  obtain ⟨-, -, -, hrho, -, -, -, -⟩ := te_ring hg hir
  obtain ⟨-, -, hdd⟩ := TabB.angleSound g hg.2.2.1 hg.2.2.2.1
  obtain ⟨hcx, hsy, -, -⟩ := hdd j hj
  rw [te_cen_rcell hg ir hj]
  have hsh : secRho ((gR g).rad ir) ((gR g).rad (ir + 1)) (j * (π / g.NT)) ((j + 1) * (π / g.NT)) =
      secRho ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT) := by
    rw [show ((j : ℝ) + 1) * (π / g.NT) = j * (π / g.NT) + π / g.NT by ring]; exact secRho_shift _ _ _ _
  have hang : (j * (π / g.NT) + (j + 1) * (π / g.NT)) / 2 = (2 * j + 1) * (π / g.NT) / 2 := by ring
  unfold secCentroid
  rw [hsh, hang]
  rw [te_mkDData_cx] at hcx
  rw [te_mkDData_sy] at hsy
  exact ⟨Iv.mem_mul hrho hcx, Iv.mem_mul hrho hsy⟩

/-- the second moment of a relative cell about its centroid -/
lemma te_mom (hg : GridOK g) {ir : ℕ} (hir : ir < g.NR) {j : ℤ} (hj : |j| < g.NT) :
    ∫ z in rcell g ir j, sqDist z (cen (rcell g ir j)) ≤ fx (mkRing g ir).momHi * (volume (rcell g ir j)).toReal := by
  obtain ⟨-, -, -, -, hm, -, -, -⟩ := te_ring hg hir
  have h := (sectorCen _ _ _ _ (te_secOK hg ir hj)).2
  have hsh : secRho ((gR g).rad ir) ((gR g).rad (ir + 1)) (j * (π / g.NT)) ((j + 1) * (π / g.NT)) =
      secRho ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT) := by
    rw [show ((j : ℝ) + 1) * (π / g.NT) = j * (π / g.NT) + π / g.NT by ring]; exact secRho_shift _ _ _ _
  rw [hsh] at h
  have hV := te_vr_pos hg ir hj
  rw [te_vr_eq] at hV
  rw [← te_rcell_eq] at h
  rw [inv_mul_eq_iff_eq_mul₀ hV.ne'] at h
  rw [h]
  nlinarith

lemma te_momHi_nonneg (g : Grid) (ir : ℕ) : 0 ≤ fx (mkRing g ir).momHi :=
  fx_nonneg_iff.mpr (momHi_nonneg g ir)

lemma te_hull_r1 (hg : GridOK g) {ir : ℕ} (hir : ir < g.NR) :
    fx (Iv.mul (mkRing g ir).r1 (mkAData g).ch).lo ≤ (gR g).rad ir * Real.cos (π / g.NT / 2) := by
  obtain ⟨hr1, -⟩ := te_ring hg hir
  obtain ⟨hch, -, -⟩ := TabB.angleSound g hg.2.2.1 hg.2.2.2.1
  exact ivMem_lo_le (Iv.mem_mul hr1 hch)

lemma te_hull_r2 (hg : GridOK g) {ir : ℕ} (hir : ir < g.NR) : (gR g).rad (ir + 1) ≤ fx (mkRing g ir).r2.hi :=
  ivMem_hi_le (te_ring hg hir).2.1




/-! ## Distance ranges along the segments -/

lemma te_cos_half (j : ℤ) (h : ℝ) : Real.cos ((((j : ℝ) + 1) * h - j * h) / 2) = Real.cos (h / 2) := by
  congr 1; ring

/-- `|z|` along a segment from a point `m` near the centroid of a relative cell (`hullR`). -/
lemma te_seg_hullR (hg : GridOK g) {ir : ℕ} (hir : ir < g.NR) {j : ℤ} (hj : |j| < g.NT) {m : Pt} {e : ℝ}
    (hm : edist2 (cen (rcell g ir j)) m ≤ e) {E : ℤ} (hE : e ≤ fx E) :
    ∀ z ∈ rcell g ir j, ∀ t ∈ Icc (0 : ℝ) 1,
      fx (W3C.hullR (mkRing g ir) (mkAData g).ch (E + 1)).1 ≤ enorm2 (m + t • (z - m)) ∧
      enorm2 (m + t • (z - m)) ≤ fx (W3C.hullR (mkRing g ir) (mkAData g).ch (E + 1)).2 := by
  intro z hz t ht
  rw [te_cen_rcell hg ir hj] at hm
  obtain ⟨h1, h2⟩ := seg_norm (te_secOK hg ir hj) hz ht m hm
  rw [te_cos_half] at h1
  have hr1 := te_hull_r1 hg hir
  have hr2 := te_hull_r2 hg hir
  have h1' : (π / (g.NT : ℝ)) / 2 = π / g.NT / 2 := rfl
  simp only [W3C.hullR, te_fx_sub, te_fx_add]
  constructor <;> linarith [te_fx_one_pos]

/-- `|z + z'|` along a segment from points near the centroids of two relative cells `(i1, j)`, `(i2, j + d)`
(`hsAt`: the polar-box bound on the hulls, rotated by `j`). -/
lemma te_seg_hs (hg : GridOK g) {i1 i2 : ℕ} (hi1 : i1 < g.NR) (hi2 : i2 < g.NR) {j d : ℤ} (hj : |j| < g.NT)
    (hd : |d| < g.NT) (hjd : |j + d| < g.NT) {m : Pt} {e : ℝ} (hm : edist2 (cen (rcell g i1 j)) m ≤ e) {E : ℤ}
    (hE : e ≤ fx E) :
    ∀ z ∈ rcell g i1 j, ∀ z' ∈ rcell g i2 (j + d), ∀ t ∈ Icc (0 : ℝ) 1,
      fx (W3C.hsAt (W3C.mkTabData g) i1 i2 d (E + 1)).1 ≤
        enorm2 ((m + t • (z - m)) + (cen (rcell g i2 (j + d)) + t • (z' - cen (rcell g i2 (j + d))))) ∧
      enorm2 ((m + t • (z - m)) + (cen (rcell g i2 (j + d)) + t • (z' - cen (rcell g i2 (j + d))))) ≤
        fx (W3C.hsAt (W3C.mkTabData g) i1 i2 d (E + 1)).2 := by
  intro z hz z' hz' t ht
  set h := π / (g.NT : ℝ) with hhdef
  have hZ := te_secOK hg i1 hj
  have hZ' := te_secOK hg i2 hjd
  have hhpos : 0 < h := by have := hZ.2.2.2.1; nlinarith
  have hNh : h * (g.NT : ℝ) = π := by
    have hN0 : (g.NT : ℝ) ≠ 0 := by have := hg.2.2.1; exact_mod_cast (show g.NT ≠ 0 by omega)
    rw [hhdef, div_mul_cancel₀ π hN0]
  rw [te_cen_rcell hg i1 hj] at hm
  have hm' : edist2 (secCentroid ((gR g).rad i2) ((gR g).rad (i2 + 1)) (↑(j + d) * h) ((↑(j + d) + 1) * h))
      (cen (rcell g i2 (j + d))) ≤ 0 := by
    rw [te_cen_rcell hg i2 hjd, hhdef]; unfold edist2 sqDist; simp
  obtain ⟨ρ, φ, hρ1, hρ2, hφ1, hφ2, hXP⟩ := seg_hull hZ hz ht m hm
  obtain ⟨ρ', φ', hρ'1, hρ'2, hφ'1, hφ'2, hYQ⟩ := seg_hull hZ' hz' ht _ hm'
  rw [te_cos_half] at hρ1 hρ'1
  -- the angle between the two hull points (rotated by `j h`)
  obtain ⟨-, -, hdd⟩ := TabB.angleSound g hg.2.2.1 hg.2.2.2.1
  obtain ⟨-, -, mcmin, mcmax⟩ := hdd d hd
  have hφa : 0 ≤ φ - j * h := by linarith
  have hφb : φ - j * h ≤ h := by linarith
  have hφ'a : d * h ≤ φ' - j * h := by push_cast at hφ'1; linarith
  have hφ'b : φ' - j * h ≤ (d + 1) * h := by push_cast at hφ'2; linarith
  obtain ⟨hc1, hc2⟩ := TabB.angleRange h d g.NT hhpos hNh hd (φ - j * h) (φ' - j * h) hφa hφb hφ'a hφ'b
  rw [show φ' - j * h - (φ - j * h) = φ' - φ by ring] at hc1 hc2
  have hc2' : (if |d| ≤ 1 then (1 : ℝ) else Real.cos ((|d| - 1) * h)) ≤ 1 := by
    split_ifs; exacts [le_rfl, Real.cos_le_one _]
  have hcosh : 0 ≤ Real.cos (h / 2) := by
    have := cos_half_nonneg hZ; rwa [te_cos_half] at this
  obtain ⟨hr1, hr2, -⟩ := te_ring hg hi1
  obtain ⟨hq1, hq2, -⟩ := te_ring hg hi2
  obtain ⟨hch, -, -⟩ := TabB.angleSound g hg.2.2.1 hg.2.2.2.1
  have hmr1h : ivMem ((gR g).rad i1 * Real.cos (h / 2)) (Iv.mul (mkRing g i1).r1 (mkAData g).ch) :=
    Iv.mem_mul hr1 hch
  have hmq1h : ivMem ((gR g).rad i2 * Real.cos (h / 2)) (Iv.mul (mkRing g i2).r1 (mkAData g).ch) :=
    Iv.mem_mul hq1 hch
  have hF := TabB.frangeSound (Iv.mul (mkRing g i1).r1 (mkAData g).ch) (mkRing g i1).r2
    (Iv.mul (mkRing g i2).r1 (mkAData g).ch) (mkRing g i2).r2 (mkDData g d).cmin (mkDData g d).cmax
    ((gR g).rad i1 * Real.cos (h / 2)) ((gR g).rad (i1 + 1)) ((gR g).rad i2 * Real.cos (h / 2))
    ((gR g).rad (i2 + 1)) _ _ hmr1h hr2 hmq1h hq2 mcmin mcmax (mul_nonneg hZ.1 hcosh) (mul_nonneg hZ'.1 hcosh)
    (Real.neg_one_le_cos _) hc2' ρ ρ' (Real.cos (φ' - φ)) hρ1 hρ2 hρ'1 hρ'2 hc1 hc2
  obtain ⟨hF1, hF2⟩ := hF
  set X := m + t • (z - m)
  set Y := cen (rcell g i2 (j + d)) + t • (z' - cen (rcell g i2 (j + d)))
  set P : Pt := (ρ * Real.cos φ, ρ * Real.sin φ)
  set Q : Pt := (ρ' * Real.cos φ', ρ' * Real.sin φ')
  have hPQ := enorm2_polar_add_sq ρ φ ρ' φ'
  have hdiff : |enorm2 (X + Y) - enorm2 (P + Q)| ≤ e := by
    refine (abs_enorm2_sub_le _ _).trans ?_
    rw [show X + Y - (P + Q) = (X - P) + (Y - Q) by abel]
    exact (enorm2_add_le _ _).trans (by linarith [hXP, hYQ])
  have hnn : 0 ≤ enorm2 (P + Q) := enorm2_nonneg _
  set hh := frange (Iv.mul (mkRing g i1).r1 (mkAData g).ch) (mkRing g i1).r2
    (Iv.mul (mkRing g i2).r1 (mkAData g).ch) (mkRing g i2).r2 (mkDData g d).cmin (mkDData g d).cmax with hhh
  have hlo : √(fx (Max.max hh.1 0)) ≤ enorm2 (P + Q) := by
    rw [te_fx_max, te_fx_zero]
    calc √(max (fx hh.1) 0) ≤ √(enorm2 (P + Q) ^ 2) :=
          Real.sqrt_le_sqrt (max_le (by rw [hPQ]; exact hF1) (sq_nonneg _))
      _ = enorm2 (P + Q) := Real.sqrt_sq hnn
  have hhi : enorm2 (P + Q) ≤ √(fx hh.2) := by
    calc enorm2 (P + Q) = √(enorm2 (P + Q) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ √(fx hh.2) := Real.sqrt_le_sqrt (by rw [hPQ]; exact hF2)
  have hsl := sqrt_pt_lo (Max.max hh.1 0)
  have hsh := sqrt_pt_hi hh.2
  rw [te_hsAt g hi1 hi2 hd]
  have hcode : W3C.hullSum0 g (mkRing g i1) (mkRing g i2) (mkAData g).ch d =
      ((Iv.sqrt ⟨Max.max hh.1 0, Max.max hh.1 0⟩).lo - 0, (Iv.sqrt ⟨hh.2, hh.2⟩).hi + 0) := rfl
  rw [hcode]
  simp only [te_fx_sub, te_fx_add, te_fx_zero]
  have habs := abs_le.mp hdiff
  constructor <;> linarith [te_fx_one_pos]

/-! ## The centroid lies in the closed convex hull; the range of `|z_a + z_b + z_c|` along a segment -/

lemma te_cen_mem_hull {W : Set Pt} (hWm : MeasurableSet W) (hW0 : volume W ≠ 0) (hWt : volume W ≠ ⊤)
    (hWb : Bornology.IsBounded W) : cen W ∈ closure (convexHull ℝ W) := by
  have hint : IntegrableOn (fun x : Pt => x) W :=
    (continuous_id.continuousOn.integrableOn_compact hWb.isCompact_closure).mono_set subset_closure
  have h := (convex_convexHull ℝ W).set_average_mem_closure (μ := volume) (t := W) (f := fun x : Pt => x) hW0 hWt
    ((ae_restrict_mem hWm).mono fun x hx => subset_convexHull ℝ W hx) hint
  convert h using 1
  rw [setAverage_eq, measureReal_def]
  ext
  · simp only [cen, Prod.smul_fst, smul_eq_mul]
    rw [fst_integral hint]
  · simp only [cen, Prod.smul_snd, smul_eq_mul]
    rw [snd_integral hint]

lemma te_seg_mem_hull {W : Set Pt} (hWm : MeasurableSet W) (hW0 : volume W ≠ 0) (hWt : volume W ≠ ⊤)
    (hWb : Bornology.IsBounded W) {z : Pt} (hz : z ∈ W) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cen W + t • (z - cen W) ∈ closure (convexHull ℝ W) :=
  (convex_convexHull ℝ W).closure.add_smul_sub_mem (te_cen_mem_hull hWm hW0 hWt hWb)
    (subset_closure (subset_convexHull ℝ W hz)) ht

/-- `|z_a + z_b + z_c|` along a segment from a point `m` near the sum of the centroids (`TriRangeSound` on the closed
convex hulls). -/
lemma te_seg_tri (hg : GridOK g) (hTR : TriRangeSound) {ia ib ic : ℕ} (hia : ia < g.NR) (hib : ib < g.NR)
    (hic : ic < g.NR) {dab dbc : ℤ} (hab : |dab| < g.NT) (hbc : |dbc| < g.NT) (habc : |dab + dbc| < g.NT)
    {m : Pt} {e : ℝ}
    (hm : edist2 (cen (rcell g ia 0) + cen (rcell g ib dab) + cen (rcell g ic (dab + dbc))) m ≤ e) :
    ∀ u ∈ rcell g ia 0, ∀ v ∈ rcell g ib dab, ∀ w ∈ rcell g ic (dab + dbc), ∀ t ∈ Icc (0 : ℝ) 1,
      fx (W3C.triRange28 (W3C.geoAt g (W3C.mkTabData g).geo ia 0).pv (W3C.geoAt g (W3C.mkTabData g).geo ib dab).pv
          (W3C.geoAt g (W3C.mkTabData g).geo ic (dab + dbc)).pv).1 - e ≤ enorm2 (m + t • ((w + (u + v)) - m)) ∧
      enorm2 (m + t • ((w + (u + v)) - m)) ≤
        fx (W3C.triRange28 (W3C.geoAt g (W3C.mkTabData g).geo ia 0).pv (W3C.geoAt g (W3C.mkTabData g).geo ib dab).pv
          (W3C.geoAt g (W3C.mkTabData g).geo ic (dab + dbc)).pv).2 + e := by
  intro u hu v hv w hw t ht
  have h0 : |(0 : ℤ)| < g.NT := by simp only [abs_zero, Nat.cast_pos]; have := hg.2.2.1; omega
  set Ca := cen (rcell g ia 0)
  set Cb := cen (rcell g ib dab)
  set Cc := cen (rcell g ic (dab + dbc))
  have hXa := te_seg_mem_hull (te_rcell_meas hg ia h0) (te_rcell_ne0 hg ia h0) (te_rcell_netop hg ia h0)
    (te_rcell_bdd hg ia h0) hu ht
  have hXb := te_seg_mem_hull (te_rcell_meas hg ib hab) (te_rcell_ne0 hg ib hab) (te_rcell_netop hg ib hab)
    (te_rcell_bdd hg ib hab) hv ht
  have hXc := te_seg_mem_hull (te_rcell_meas hg ic habc) (te_rcell_ne0 hg ic habc) (te_rcell_netop hg ic habc)
    (te_rcell_bdd hg ic habc) hw ht
  obtain ⟨h1, h2⟩ := hTR g hg ia ib ic dab dbc hia hib hic hab hbc habc _ hXa _ hXb _ hXc
  have hdiff : |enorm2 (m + t • ((w + (u + v)) - m)) -
      enorm2 ((Ca + t • (u - Ca)) + (Cb + t • (v - Cb)) + (Cc + t • (w - Cc)))| ≤ e := by
    refine (abs_enorm2_sub_le _ _).trans ?_
    have e1 : m + t • ((w + (u + v)) - m) - ((Ca + t • (u - Ca)) + (Cb + t • (v - Cb)) + (Cc + t • (w - Cc))) =
        (1 - t) • (m - (Ca + Cb + Cc)) := by
      ext <;> simp <;> ring
    rw [e1, enorm2_smul, abs_of_nonneg (by linarith [ht.2])]
    have hm' : enorm2 (m - (Ca + Cb + Cc)) ≤ e := by
      rw [show m - (Ca + Cb + Cc) = -((Ca + Cb + Cc) - m) by abel, te_enorm2_neg]; exact hm
    calc (1 - t) * enorm2 (m - (Ca + Cb + Cc)) ≤ 1 * enorm2 (m - (Ca + Cb + Cc)) :=
          mul_le_mul_of_nonneg_right (by linarith [ht.1]) (enorm2_nonneg _)
      _ ≤ e := by rw [one_mul]; exact hm'
  have habs := abs_le.mp hdiff
  constructor <;> linarith

/-! ## The union areas of the configurations -/

lemma te_unionArea_lv3 (a b : Pt) : unionArea ![-(a + b), -b, (0 : Pt)] = A2 a b + π + A1 a := by
  have ht := unionArea_translate b ![-(a + b), -b, (0 : Pt)]
  have e : (fun i => ![-(a + b), -b, (0 : Pt)] i + b) = ![-a, (0 : Pt), b] := by
    funext i; fin_cases i <;> simp <;> abel
  rw [e] at ht
  rw [← ht, a2Union a b]; ring

lemma te_unionArea_lv3_ge (a b : Pt) : π + A1 b ≤ unionArea ![-(a + b), -b, (0 : Pt)] := by
  have e2 : (volume (disk 0 1 ∪ disk (-b) 1)).toReal = π + A1 b := by
    rw [← tp_A1_neg, tp_A1_eq_union]
    unfold unionArea
    rw [tp_iUnion_two]
    ring
  rw [← e2]
  unfold unionArea
  rw [tp_iUnion_three]
  apply ENNReal.toReal_mono
  · exact measure_union_ne_top (measure_union_ne_top (tp_volume_disk_ne_top _) (tp_volume_disk_ne_top _))
      (tp_volume_disk_ne_top _)
  · apply measure_mono
    intro x hx
    rcases hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl (Or.inr hx)

end Cells

end BHH.W3
