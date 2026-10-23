/-
The triple part of the window-3 table soundness (fields `a3`, `tc` of `TableSound3` for the data `discOf3`): module
D2 (`TripleSound`) in the relative frame with the symmetrised pair entries of the computation (W2's entry bound for
`ā_2`, module D1 `LV3Sound` for `LV3LO`), moved to the grid cells by a rotation (`RotA3`; computed half of the
triple table) or by a reflection and a rotation (`ReflA3`, `RotA3`; mirror half).  The stored value `2 · a48 + T`
gives `ā_3 = a48 · 2^-48 ≥ fx(abar3)` and the T class.
-/
import W3.TabSound3Pair

open MeasureTheory Set Real

namespace BHH.W3.TabSound3

open W2C BHH.Cert BHH BHH.W2

lemma rcell_zero (g : Grid) (ir : ℕ) :
    rcell g ir 0 = sector ((gR g).rad ir) ((gR g).rad (ir + 1)) 0 (π / g.NT) := by
  unfold rcell; simp

lemma ang_eq (g : Grid) (i : ℕ) : (gR g).ang i = -(π / 2) + i * (π / g.NT) := by
  show GridR.ang ⟨g.N1, g.N2, g.NT⟩ i = _
  unfold GridR.ang; simp only; ring

lemma vr_eq (g : Grid) (h1 : 0 < g.N1) (h2 : 0 < g.N2) (hNT : 2 ≤ g.NT) (ir : ℕ) {j : ℤ} (hj : |j| < g.NT) :
    vr g ir j = ((gR g).rad (ir + 1) ^ 2 - (gR g).rad ir ^ 2) * (π / g.NT) / 2 := by
  unfold vr rcell
  rw [volume_sector_toReal (secOK_z' g h1 h2 hNT ir hj)]
  ring

lemma vol_cell_eq (g : Grid) (h1 : 0 < g.N1) (h2 : 0 < g.N2) (hNT : 2 ≤ g.NT) (ir : ℕ) {it : ℕ}
    (hit : it < g.NT) :
    (volume ((gR g).cell ir it)).toReal = ((gR g).rad (ir + 1) ^ 2 - (gR g).rad ir ^ 2) * (π / g.NT) / 2 := by
  rw [TSO.cell_eq_sector, volume_sector_toReal (TSO.secOK_cell g h1 h2 hNT ir hit), TSO.ang_succ]
  ring

lemma vol_cell_eq_vr (g : Grid) (h1 : 0 < g.N1) (h2 : 0 < g.N2) (hNT : 2 ≤ g.NT) (ir : ℕ) {it : ℕ}
    (hit : it < g.NT) {j : ℤ} (hj : |j| < g.NT) : (volume ((gR g).cell ir it)).toReal = vr g ir j := by
  rw [vol_cell_eq g h1 h2 hNT ir hit, vr_eq g h1 h2 hNT ir hj]

/-- rotating the cell `(ir, it)` by `-θ_ita` gives the relative cell `(ir, it - ita)` -/
lemma cell_rot (g : Grid) (ir it ita : ℕ) :
    sector ((gR g).rad ir) ((gR g).rad (ir + 1)) ((gR g).ang it + -(gR g).ang ita)
      ((gR g).ang (it + 1) + -(gR g).ang ita) = rcell g ir ((it : ℤ) - ita) := by
  unfold rcell
  congr 1
  · rw [ang_eq, ang_eq]; push_cast; ring
  · rw [ang_eq, ang_eq]; push_cast; ring

/-- reflecting the cell `(ir, it)` and rotating by `θ_{ita+1}` gives the relative cell `(ir, ita - it)` -/
lemma cell_refl_rot (g : Grid) (ir it ita : ℕ) :
    sector ((gR g).rad ir) ((gR g).rad (ir + 1)) (-(gR g).ang (it + 1) + (gR g).ang (ita + 1))
      (-(gR g).ang it + (gR g).ang (ita + 1)) = rcell g ir ((ita : ℤ) - it) := by
  unfold rcell
  congr 1
  · rw [ang_eq, ang_eq]; push_cast; ring
  · rw [ang_eq, ang_eq]; push_cast; ring

/-- The relative-frame triple bound (module D2 with the pair entries of the computation). -/
theorem relTriple (hTS : TripleSound) (hLV : LV3Sound) (hG : GreenFormula) (hV : VertexLemmaSeg) {g : Grid}
    (hok : GridOK g) (hnd : nondegOK g = true) {ia ib ic : ℕ} (hia : ia < g.NR) (hib : ib < g.NR)
    (hic : ic < g.NR) {dab dbc : ℤ} (hab : |dab| < g.NT) (hbc : |dbc| < g.NT) (habc : |dab + dbc| < g.NT) :
    ((triEnt g ia ib ic dab dbc).tcls = true →
        ∀ u ∈ rcell g ia 0, ∀ v ∈ rcell g ib dab, ∀ w ∈ rcell g ic (dab + dbc), sqDist (u + v + w) 0 ≤ 1) ∧
    ∫ p in rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), A3 p.1 p.2.1 p.2.2 ≤
      fx (triEnt g ia ib ic dab dbc).abar3 * vr g ia 0 * vr g ib dab * vr g ic (dab + dbc) := by
  have hEB := entryBound3 hG hV hok hnd
  have hbcm : |-dbc| < g.NT := by rwa [abs_neg]
  have habm : |-dab| < g.NT := by rwa [abs_neg]
  refine hTS hG hV g hok ia ib ic dab dbc _ _ hia hib hic hab hbc habc ?_ ?_
  · -- the pair entry `(ib, ic, dbc)`: `ā_2` of the symmetrised entry is at least the raw entry
    have he := hEB ib ic hib hic dbc hbc
    have hv1 := ENNReal.toReal_nonneg (a := volume (rcell g ib 0))
    have hv2 := ENNReal.toReal_nonneg (a := volume (rcell g ic dbc))
    unfold vr
    rw [rcell_zero] at hv1 ⊢
    unfold rcell at hv2 ⊢
    refine he.trans ?_
    apply mul_le_mul_of_nonneg_right _ hv2
    apply mul_le_mul_of_nonneg_right _ hv1
    apply fx_le_iff.mpr
    rw [pairEntryF_eq g hbc, pairEntryF_eq g hbcm]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  · -- the pair entry `(ia, ib, dab)`: `LV3LO` of the symmetrised entry is at most the raw one
    have hl := hLV hG hV g hok ia ib dab hia hib hab
    refine le_trans ?_ hl
    have hv1 := ENNReal.toReal_nonneg (a := volume (rcell g ia 0))
    have hv2 := ENNReal.toReal_nonneg (a := volume (rcell g ib dab))
    apply mul_le_mul_of_nonneg_right _ hv2
    apply mul_le_mul_of_nonneg_right _ hv1
    apply fx_le_iff.mpr
    rw [pairEntryF_eq g hab, pairEntryF_eq g habm]
    exact min_le_left _ _


lemma ang_pm (g : Grid) (hNT : 2 ≤ g.NT) {i : ℕ} (hi : i ≤ g.NT) :
    -(π / 2) ≤ (gR g).ang i ∧ (gR g).ang i ≤ π / 2 :=
  ⟨(gR g).ang_ge (show 0 < (gR g).NT from by show 0 < g.NT; omega) i,
   (gR g).ang_le (show 0 < (gR g).NT from by show 0 < g.NT; omega) hi⟩

/-- the integral of `A_3` over three grid cells equals the one over the relative cells (rotation by `-θ_ita`) -/
lemma int_rot (hRot : RotA3) (g : Grid) (hNT : 2 ≤ g.NT) (ia ib ic : ℕ) {ita itb itc : ℕ} (hita : ita < g.NT)
    (hitb : itb < g.NT) (hitc : itc < g.NT) :
    ∫ p in (gR g).cell ia ita ×ˢ ((gR g).cell ib itb ×ˢ (gR g).cell ic itc), A3 p.1 p.2.1 p.2.2 =
      ∫ p in rcell g ia 0 ×ˢ (rcell g ib ((itb : ℤ) - ita) ×ˢ rcell g ic ((itc : ℤ) - ita)),
        A3 p.1 p.2.1 p.2.2 := by
  have pa := ang_pm g hNT hita.le
  have pa1 := ang_pm g hNT (show ita + 1 ≤ g.NT by omega)
  have pb := ang_pm g hNT hitb.le
  have pb1 := ang_pm g hNT (show itb + 1 ≤ g.NT by omega)
  have pc := ang_pm g hNT hitc.le
  have pc1 := ang_pm g hNT (show itc + 1 ≤ g.NT by omega)
  have hpi := Real.pi_pos
  have h := hRot ((gR g).rad ia) ((gR g).rad (ia + 1)) ((gR g).ang ita) ((gR g).ang (ita + 1))
    ((gR g).rad ib) ((gR g).rad (ib + 1)) ((gR g).ang itb) ((gR g).ang (itb + 1))
    ((gR g).rad ic) ((gR g).rad (ic + 1)) ((gR g).ang itc) ((gR g).ang (itc + 1)) (-(gR g).ang ita)
    ((gR g).rad_nonneg ia) ((gR g).rad_nonneg ib) ((gR g).rad_nonneg ic)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  rw [cell_rot, cell_rot, cell_rot, sub_self] at h
  exact h

/-- the integral of `A_3` over three grid cells equals the one over the relative cells of the mirror triple
(reflection, then rotation by `θ_{ita+1}`) -/
lemma int_refl (hRot : RotA3) (hRefl : ReflA3) (g : Grid) (hNT : 2 ≤ g.NT) (ia ib ic : ℕ) {ita itb itc : ℕ}
    (hita : ita < g.NT) (hitb : itb < g.NT) (hitc : itc < g.NT) :
    ∫ p in (gR g).cell ia ita ×ˢ ((gR g).cell ib itb ×ˢ (gR g).cell ic itc), A3 p.1 p.2.1 p.2.2 =
      ∫ p in rcell g ia 0 ×ˢ (rcell g ib ((ita : ℤ) - itb) ×ˢ rcell g ic ((ita : ℤ) - itc)),
        A3 p.1 p.2.1 p.2.2 := by
  have pa := ang_pm g hNT hita.le
  have pa1 := ang_pm g hNT (show ita + 1 ≤ g.NT by omega)
  have pb := ang_pm g hNT hitb.le
  have pb1 := ang_pm g hNT (show itb + 1 ≤ g.NT by omega)
  have pc := ang_pm g hNT hitc.le
  have pc1 := ang_pm g hNT (show itc + 1 ≤ g.NT by omega)
  have hpi := Real.pi_pos
  have h1 := (hRefl ((gR g).rad ia) ((gR g).rad (ia + 1)) ((gR g).ang ita) ((gR g).ang (ita + 1))
    ((gR g).rad ib) ((gR g).rad (ib + 1)) ((gR g).ang itb) ((gR g).ang (itb + 1))
    ((gR g).rad ic) ((gR g).rad (ic + 1)) ((gR g).ang itc) ((gR g).ang (itc + 1))
    ((gR g).rad_nonneg ia) ((gR g).rad_nonneg ib) ((gR g).rad_nonneg ic)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)).1
  have h2 := hRot ((gR g).rad ia) ((gR g).rad (ia + 1)) (-(gR g).ang (ita + 1)) (-(gR g).ang ita)
    ((gR g).rad ib) ((gR g).rad (ib + 1)) (-(gR g).ang (itb + 1)) (-(gR g).ang itb)
    ((gR g).rad ic) ((gR g).rad (ic + 1)) (-(gR g).ang (itc + 1)) (-(gR g).ang itc) ((gR g).ang (ita + 1))
    ((gR g).rad_nonneg ia) ((gR g).rad_nonneg ib) ((gR g).rad_nonneg ic)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  rw [cell_refl_rot, cell_refl_rot, cell_refl_rot, sub_self] at h2
  rw [TSO.cell_eq_sector, TSO.cell_eq_sector, TSO.cell_eq_sector, h1, h2]


lemma stv_div (te : W3C.TripE) : stv te / 2 = W3C.up48 te.abar3 := by
  unfold stv; split_ifs <;> omega

lemma stv_mod (te : W3C.TripE) : (stv te % 2 == 1) = te.tcls := by
  unfold stv
  cases te.tcls
  · simp
  · simp only [ite_true]
    have : (2 * W3C.up48 te.abar3 + 1) % 2 = 1 := by omega
    simp [this]

lemma discOf3_a3 (g : Grid) (dtl : ℕ) {ia ib ic : ℕ} (hia : ia < g.NR) (hib : ib < g.NR) (hic : ic < g.NR)
    {dab dbc : ℤ} (hab : |dab| < g.NT) (hbc : |dbc| < g.NT) :
    (discOf3 g dtl).a3 ia ib ic dab dbc =
      if 0 < dbc ∨ (dbc = 0 ∧ 0 ≤ dab) then ((W3C.up48 (triEnt g ia ib ic dab dbc).abar3 : ℕ) : ℝ) / 2 ^ 48
      else ((W3C.up48 (triEnt g ia ib ic (-dab) (-dbc)).abar3 : ℕ) : ℝ) / 2 ^ 48 := by
  simp only [discOf3]
  rw [tri_getD g hia hib hic hab hbc]
  split_ifs <;> rw [stv_div]

lemma discOf3_tc (g : Grid) (dtl : ℕ) {ia ib ic : ℕ} (hia : ia < g.NR) (hib : ib < g.NR) (hic : ic < g.NR)
    {dab dbc : ℤ} (hab : |dab| < g.NT) (hbc : |dbc| < g.NT) :
    (discOf3 g dtl).tc ia ib ic dab dbc =
      if 0 < dbc ∨ (dbc = 0 ∧ 0 ≤ dab) then (triEnt g ia ib ic dab dbc).tcls
      else (triEnt g ia ib ic (-dab) (-dbc)).tcls := by
  simp only [discOf3]
  rw [tri_getD g hia hib hic hab hbc]
  split_ifs <;> rw [stv_mod]


/-- The `a3` field of `TableSound3` for the data `discOf3`. -/
theorem a3Part (hTS : TripleSound) (hLV : LV3Sound) (hRot : RotA3) (hRefl : ReflA3) (hG : GreenFormula)
    (hV : VertexLemmaSeg) {g : Grid} (dtl : ℕ) (hok : GridOK g) (hnd : nondegOK g = true) :
    ∀ ia ib ic ita itb itc, ia < (gR g).NR → ib < (gR g).NR → ic < (gR g).NR → ita < (gR g).NT →
      itb < (gR g).NT → itc < (gR g).NT →
      ∫ p in (gR g).cell ia ita ×ˢ ((gR g).cell ib itb ×ˢ (gR g).cell ic itc), A3 p.1 p.2.1 p.2.2 ≤
        (discOf3 g dtl).a3 ia ib ic ((itb : ℤ) - ita) ((itc : ℤ) - itb) * (volume ((gR g).cell ia ita)).toReal *
          (volume ((gR g).cell ib itb)).toReal * (volume ((gR g).cell ic itc)).toReal := by
  intro ia ib ic ita itb itc hia hib hic hita hitb hitc
  have hok' := hok
  obtain ⟨h1, h2, hNT, -, -, -, -⟩ := hok'
  change ia < g.NR at hia
  change ib < g.NR at hib
  change ic < g.NR at hic
  change ita < g.NT at hita
  change itb < g.NT at hitb
  change itc < g.NT at hitc
  have hab : |(itb : ℤ) - ita| < g.NT := by rw [abs_lt]; constructor <;> omega
  have hbc : |(itc : ℤ) - itb| < g.NT := by rw [abs_lt]; constructor <;> omega
  have habc : |((itb : ℤ) - ita) + ((itc : ℤ) - itb)| < g.NT := by rw [abs_lt]; constructor <;> omega
  have hab' : |-((itb : ℤ) - ita)| < g.NT := by rwa [abs_neg]
  have hbc' : |-((itc : ℤ) - itb)| < g.NT := by rwa [abs_neg]
  have habc' : |-((itb : ℤ) - ita) + -((itc : ℤ) - itb)| < g.NT := by rw [abs_lt]; constructor <;> omega
  have h0 : |(0 : ℤ)| < g.NT := by rw [abs_zero]; omega
  rw [discOf3_a3 g dtl hia hib hic hab hbc]
  split_ifs with hc
  · obtain ⟨-, hI⟩ := relTriple hTS hLV hG hV hok hnd hia hib hic hab hbc habc
    rw [int_rot hRot g hNT ia ib ic hita hitb hitc]
    have e : (itc : ℤ) - ita = ((itb : ℤ) - ita) + ((itc : ℤ) - itb) := by ring
    rw [e]
    refine hI.trans ?_
    rw [vol_cell_eq_vr g h1 h2 hNT ia hita h0, vol_cell_eq_vr g h1 h2 hNT ib hitb hab,
      vol_cell_eq_vr g h1 h2 hNT ic hitc habc]
    have v1 : 0 ≤ vr g ia 0 := ENNReal.toReal_nonneg
    have v2 : 0 ≤ vr g ib ((itb : ℤ) - ita) := ENNReal.toReal_nonneg
    have v3 : 0 ≤ vr g ic (((itb : ℤ) - ita) + ((itc : ℤ) - itb)) := ENNReal.toReal_nonneg
    apply mul_le_mul_of_nonneg_right _ v3
    apply mul_le_mul_of_nonneg_right _ v2
    apply mul_le_mul_of_nonneg_right _ v1
    exact fx_le_up48 _
  · obtain ⟨-, hI⟩ := relTriple hTS hLV hG hV hok hnd hia hib hic hab' hbc' habc'
    rw [int_refl hRot hRefl g hNT ia ib ic hita hitb hitc]
    have e1 : (ita : ℤ) - itb = -((itb : ℤ) - ita) := by ring
    have e2 : (ita : ℤ) - itc = -((itb : ℤ) - ita) + -((itc : ℤ) - itb) := by ring
    rw [e1, e2]
    refine hI.trans ?_
    rw [vol_cell_eq_vr g h1 h2 hNT ia hita h0, vol_cell_eq_vr g h1 h2 hNT ib hitb hab',
      vol_cell_eq_vr g h1 h2 hNT ic hitc habc']
    have v1 : 0 ≤ vr g ia 0 := ENNReal.toReal_nonneg
    have v2 : 0 ≤ vr g ib (-((itb : ℤ) - ita)) := ENNReal.toReal_nonneg
    have v3 : 0 ≤ vr g ic (-((itb : ℤ) - ita) + -((itc : ℤ) - itb)) := ENNReal.toReal_nonneg
    apply mul_le_mul_of_nonneg_right _ v3
    apply mul_le_mul_of_nonneg_right _ v2
    apply mul_le_mul_of_nonneg_right _ v1
    exact fx_le_up48 _


/-- rotating three points by a common angle keeps the distance of their sum from `0` -/
lemma sqDist_rot3 (ρ1 ρ2 ρ3 φ1 φ2 φ3 α : ℝ) :
    sqDist (polarCoord.symm (ρ1, φ1 - α) + polarCoord.symm (ρ2, φ2 - α) + polarCoord.symm (ρ3, φ3 - α)) 0 =
      sqDist (polarCoord.symm (ρ1, φ1) + polarCoord.symm (ρ2, φ2) + polarCoord.symm (ρ3, φ3)) 0 := by
  simp only [polarCoord_symm_apply, sqDist, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, sub_zero,
    Real.cos_sub, Real.sin_sub]
  linear_combination ((ρ1 * Real.cos φ1 + ρ2 * Real.cos φ2 + ρ3 * Real.cos φ3) ^ 2 +
    (ρ1 * Real.sin φ1 + ρ2 * Real.sin φ2 + ρ3 * Real.sin φ3) ^ 2) * Real.cos_sq_add_sin_sq α

/-- reflecting three points in the real axis and rotating them by a common angle keeps the distance of their sum
from `0` -/
lemma sqDist_refl3 (ρ1 ρ2 ρ3 φ1 φ2 φ3 α : ℝ) :
    sqDist (polarCoord.symm (ρ1, α - φ1) + polarCoord.symm (ρ2, α - φ2) + polarCoord.symm (ρ3, α - φ3)) 0 =
      sqDist (polarCoord.symm (ρ1, φ1) + polarCoord.symm (ρ2, φ2) + polarCoord.symm (ρ3, φ3)) 0 := by
  simp only [polarCoord_symm_apply, sqDist, Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero, sub_zero,
    Real.cos_sub, Real.sin_sub]
  linear_combination ((ρ1 * Real.cos φ1 + ρ2 * Real.cos φ2 + ρ3 * Real.cos φ3) ^ 2 +
    (ρ1 * Real.sin φ1 + ρ2 * Real.sin φ2 + ρ3 * Real.sin φ3) ^ 2) * Real.cos_sq_add_sin_sq α

/-- a point of the cell `(ir, it)` rotated by `-θ_ita` lies in the relative cell `(ir, it - ita)` -/
lemma mem_rcell_rot (g : Grid) (ir it ita : ℕ) {ρ φ : ℝ} (hρ : ρ ∈ Ioo ((gR g).rad ir) ((gR g).rad (ir + 1)))
    (hφ : φ ∈ Ioo ((gR g).ang it) ((gR g).ang (it + 1))) :
    polarCoord.symm (ρ, φ - (gR g).ang ita) ∈ rcell g ir ((it : ℤ) - ita) := by
  unfold rcell
  refine mem_image_of_mem _ ⟨hρ, ?_⟩
  rw [mem_Ioo] at hφ ⊢
  rw [ang_eq, ang_eq] at hφ
  push_cast at hφ
  rw [ang_eq]
  push_cast
  constructor
  · have e : ((it : ℝ) - ita) * (π / g.NT) = (-(π / 2) + it * (π / g.NT)) - (-(π / 2) + ita * (π / g.NT)) := by
      ring
    rw [e]; linarith [hφ.1]
  · have e : ((it : ℝ) - ita + 1) * (π / g.NT) =
        (-(π / 2) + ((it : ℝ) + 1) * (π / g.NT)) - (-(π / 2) + ita * (π / g.NT)) := by ring
    rw [e]; linarith [hφ.2]

/-- a point of the cell `(ir, it)` reflected and rotated by `θ_{ita+1}` lies in the relative cell `(ir, ita - it)` -/
lemma mem_rcell_refl (g : Grid) (ir it ita : ℕ) {ρ φ : ℝ} (hρ : ρ ∈ Ioo ((gR g).rad ir) ((gR g).rad (ir + 1)))
    (hφ : φ ∈ Ioo ((gR g).ang it) ((gR g).ang (it + 1))) :
    polarCoord.symm (ρ, (gR g).ang (ita + 1) - φ) ∈ rcell g ir ((ita : ℤ) - it) := by
  unfold rcell
  refine mem_image_of_mem _ ⟨hρ, ?_⟩
  rw [mem_Ioo] at hφ ⊢
  rw [ang_eq, ang_eq] at hφ
  push_cast at hφ
  rw [ang_eq]
  push_cast
  constructor
  · have e : ((ita : ℝ) - it) * (π / g.NT) =
        (-(π / 2) + ((ita : ℝ) + 1) * (π / g.NT)) - (-(π / 2) + ((it : ℝ) + 1) * (π / g.NT)) := by ring
    rw [e]; linarith [hφ.2]
  · have e : ((ita : ℝ) - it + 1) * (π / g.NT) =
        (-(π / 2) + ((ita : ℝ) + 1) * (π / g.NT)) - (-(π / 2) + it * (π / g.NT)) := by ring
    rw [e]; linarith [hφ.1]

/-- The `tc` field of `TableSound3` for the data `discOf3`. -/
theorem tcPart (hTS : TripleSound) (hLV : LV3Sound) (hG : GreenFormula) (hV : VertexLemmaSeg) {g : Grid}
    (dtl : ℕ) (hok : GridOK g) (hnd : nondegOK g = true) :
    ∀ ia ib ic ita itb itc, ia < (gR g).NR → ib < (gR g).NR → ic < (gR g).NR → ita < (gR g).NT →
      itb < (gR g).NT → itc < (gR g).NT →
      (discOf3 g dtl).tc ia ib ic ((itb : ℤ) - ita) ((itc : ℤ) - itb) = true →
        ∀ u ∈ (gR g).cell ia ita, ∀ v ∈ (gR g).cell ib itb, ∀ w ∈ (gR g).cell ic itc,
          sqDist (u + v + w) 0 ≤ 1 := by
  intro ia ib ic ita itb itc hia hib hic hita hitb hitc htc u hu v hv w hw
  change ia < g.NR at hia
  change ib < g.NR at hib
  change ic < g.NR at hic
  change ita < g.NT at hita
  change itb < g.NT at hitb
  change itc < g.NT at hitc
  have hab : |(itb : ℤ) - ita| < g.NT := by rw [abs_lt]; constructor <;> omega
  have hbc : |(itc : ℤ) - itb| < g.NT := by rw [abs_lt]; constructor <;> omega
  have habc : |((itb : ℤ) - ita) + ((itc : ℤ) - itb)| < g.NT := by rw [abs_lt]; constructor <;> omega
  have hab' : |-((itb : ℤ) - ita)| < g.NT := by rwa [abs_neg]
  have hbc' : |-((itc : ℤ) - itb)| < g.NT := by rwa [abs_neg]
  have habc' : |-((itb : ℤ) - ita) + -((itc : ℤ) - itb)| < g.NT := by rw [abs_lt]; constructor <;> omega
  rw [discOf3_tc g dtl hia hib hic hab hbc] at htc
  obtain ⟨⟨ρ1, φ1⟩, ⟨hρ1, hφ1⟩, rfl⟩ := hu
  obtain ⟨⟨ρ2, φ2⟩, ⟨hρ2, hφ2⟩, rfl⟩ := hv
  obtain ⟨⟨ρ3, φ3⟩, ⟨hρ3, hφ3⟩, rfl⟩ := hw
  split_ifs at htc with hc
  · obtain ⟨hT, -⟩ := relTriple hTS hLV hG hV hok hnd hia hib hic hab hbc habc
    have ma := mem_rcell_rot g ia ita ita hρ1 hφ1
    have mb := mem_rcell_rot g ib itb ita hρ2 hφ2
    have mc := mem_rcell_rot g ic itc ita hρ3 hφ3
    have e : (itc : ℤ) - ita = ((itb : ℤ) - ita) + ((itc : ℤ) - itb) := by ring
    rw [sub_self] at ma
    rw [e] at mc
    have := hT htc _ ma _ mb _ mc
    rwa [sqDist_rot3] at this
  · obtain ⟨hT, -⟩ := relTriple hTS hLV hG hV hok hnd hia hib hic hab' hbc' habc'
    have ma := mem_rcell_refl g ia ita ita hρ1 hφ1
    have mb := mem_rcell_refl g ib itb ita hρ2 hφ2
    have mc := mem_rcell_refl g ic itc ita hρ3 hφ3
    have e1 : (ita : ℤ) - itb = -((itb : ℤ) - ita) := by ring
    have e2 : (ita : ℤ) - itc = -((itb : ℤ) - ita) + -((itc : ℤ) - itb) := by ring
    rw [sub_self] at ma
    rw [e1] at mb
    rw [e2] at mc
    have := hT htc _ ma _ mb _ mc
    rwa [sqDist_refl3] at this

end BHH.W3.TabSound3
