/-
Window-3 entries: the integrated vertex lemma for the two configurations of the window-3 entries.

* `te_lv3_core`: `LV3LO`, the two-sided bound over `Z × Z'` for `(-(z + z'), -z', 0)` at the expansion point
  `(c0, c1, 0)`: `∫ A ≥ (A(c)⁻ - 2(e0 + e1) - Σ r) |Z| |Z'|`, with the three pair remainders `lvPairT` of the code;
* `te_tri_core`: the triple entry, the upper bound over `Z_a × Z_b × Z_c` for `(-(z_a + z_b), -z_b, 0, z_c)` at
  `(c0, c1, 0, c3)` with the six pair remainders, in the form `∫ F ≤ (A(c)⁺ + 2(e0 + e1 + e3) + Σ r - L) V` for any
  `0 ≤ F ≤ A(y) - H` with `∫ H ≥ L V` (so that no integrability of the four-disk area is needed).
The pair data (distance ranges along the segments, centroid errors, moments) are hypotheses here; they are discharged
from the code in `W3/TripleEntryLV3.lean` and `W3/TripleEntryTri.lean`.
-/
import W3.TripleEntryInt

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W3

open BHH BHH.W2 BHH.Cert

/-! ## Layer 2: `LV3LO` -/

set_option maxHeartbeats 4000000 in
/-- The two-sided vertex lemma integrated over `Z × Z'` for the configuration `(-(z + z'), -z', 0)` at the expansion
point `(c0, c1, 0)`, with the code's three pair remainders (`lvPairT`) and moment data (`momentsX`). -/
theorem te_lv3_core (hV : VertexLemmaSeg) (hAS : AsinTSound) {Z Z' : Set Pt}
    (hZm : MeasurableSet Z) (hZ'm : MeasurableSet Z')
    (hint : ∀ f : Pt × Pt → ℝ, Continuous f → IntegrableOn f (Z ×ˢ Z'))
    (hZi : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f Z) (hZ'i : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f Z')
    (hZ0 : volume Z ≠ 0) (hZt : volume Z ≠ ⊤) (hZ'0 : volume Z' ≠ 0) (hZ't : volume Z' ≠ ⊤)
    (hUint : IntegrableOn (fun p : Pt × Pt => unionArea ![-(p.1 + p.2), -p.2, (0 : Pt)]) (Z ×ˢ Z'))
    {mZ mZ' : ℝ} (hm0 : 0 ≤ mZ) (hm'0 : 0 ≤ mZ')
    (hm : ∫ z in Z, sqDist z (cen Z) ≤ mZ * (volume Z).toReal)
    (hm' : ∫ z in Z', sqDist z (cen Z') ≤ mZ' * (volume Z').toReal)
    {sqa sqb : ℤ} (hsqa : √mZ ≤ fx sqa) (hsqb : √mZ' ≤ fx sqb)
    {c0 c1 : Pt} {ep0 ep1 : ℤ} (he0 : edist2 (cen Z + cen Z') (-c0) ≤ fx ep0)
    (he1 : edist2 (cen Z') (-c1) ≤ fx ep1)
    {U : ℝ} (hU : U ≤ unionArea ![c0, c1, (0 : Pt)])
    {dna dxa dnb dxb dnc dxc ra rb rc : ℤ}
    (hra : W3C.lvPairT W3C.mkAsinTab dna dxa (W3C.momentsX [1, 2] [sqa, sqb] (ep0 + ep1)).1
      (W3C.momentsX [1, 2] [sqa, sqb] (ep0 + ep1)).2 = some ra)
    (hrb : W3C.lvPairT W3C.mkAsinTab dnb dxb (W3C.momentsX [1, 1] [sqa, sqb] ep0).1
      (W3C.momentsX [1, 1] [sqa, sqb] ep0).2 = some rb)
    (hrc : W3C.lvPairT W3C.mkAsinTab dnc dxc (W3C.momentsX [0, 1] [sqa, sqb] ep1).1
      (W3C.momentsX [0, 1] [sqa, sqb] ep1).2 = some rc)
    (hsa : ∀ p ∈ Z ×ˢ Z', ∀ t ∈ Icc (0 : ℝ) 1, fx dna ≤ enorm2 ((c1 - c0) + t • (p.1 - (c1 - c0))) ∧
      enorm2 ((c1 - c0) + t • (p.1 - (c1 - c0))) ≤ fx dxa)
    (hsb : ∀ p ∈ Z ×ˢ Z', ∀ t ∈ Icc (0 : ℝ) 1, fx dnb ≤ enorm2 (-c0 + t • ((p.1 + p.2) - -c0)) ∧
      enorm2 (-c0 + t • ((p.1 + p.2) - -c0)) ≤ fx dxb)
    (hsc : ∀ p ∈ Z ×ˢ Z', ∀ t ∈ Icc (0 : ℝ) 1, fx dnc ≤ enorm2 (-c1 + t • (p.2 - -c1)) ∧
      enorm2 (-c1 + t • (p.2 - -c1)) ≤ fx dxc) :
    (U - 2 * (fx ep0 + fx ep1) - (fx ra + fx rb + fx rc)) * ((volume Z).toReal * (volume Z').toReal) ≤
      ∫ p in Z ×ˢ Z', unionArea ![-(p.1 + p.2), -p.2, (0 : Pt)] := by
  have hVp : 0 < (volume Z).toReal := ENNReal.toReal_pos hZ0 hZt
  have hV'p : 0 < (volume Z').toReal := ENNReal.toReal_pos hZ'0 hZ't
  have hSV : (volume (Z ×ˢ Z')).toReal = (volume Z).toReal * (volume Z').toReal := te_vol2 Z Z'
  have hSt : volume (Z ×ˢ Z') ≠ ⊤ := by
    rw [Measure.volume_eq_prod (α := Pt) (β := Pt), Measure.prod_prod]; exact ENNReal.mul_ne_top hZt hZ't
  set C := cen Z with hCdef
  set C' := cen Z' with hC'def
  obtain ⟨hda, -, -⟩ := te_lvPairT_spec hAS hra
  obtain ⟨hdb, -, -⟩ := te_lvPairT_spec hAS hrb
  obtain ⟨hdc, -, -⟩ := te_lvPairT_spec hAS hrc
  -- the data of the vertex lemma
  set dlo : Fin 3 → Fin 3 → ℝ := ![![0, fx dna, fx dnb], ![0, 0, fx dnc], ![0, 0, 0]] with hdlo
  set dhi : Fin 3 → Fin 3 → ℝ := ![![0, fx dxa, fx dxb], ![0, 0, fx dxc], ![0, 0, 0]] with hdhi
  set first : Fin 3 → Fin 3 → Bool := ![![false, decide (W2C.useFirstOf dxa), decide (W2C.useFirstOf dxb)],
    ![false, false, decide (W2C.useFirstOf dxc)], ![false, false, false]] with hfirst
  set ua : Pt × Pt → ℝ := fun p => enorm2 (p.1 - C) with hua
  set ub : Pt × Pt → ℝ := fun p => enorm2 (p.2 - C') with hub
  set uc : Pt × Pt → ℝ := fun _ => 0 with huc
  have cua : Continuous ua := tp_continuous_enorm2.comp (continuous_fst.sub continuous_const)
  have cub : Continuous ub := tp_continuous_enorm2.comp (continuous_snd.sub continuous_const)
  have cuc : Continuous uc := continuous_const
  set Xa : Pt × Pt → ℝ := fun p => (1 : ℕ) * ua p + (2 : ℕ) * ub p + 0 * uc p + fx (ep0 + ep1) with hXa
  set Xb : Pt × Pt → ℝ := fun p => (1 : ℕ) * ua p + (1 : ℕ) * ub p + 0 * uc p + fx ep0 with hXb
  set Xc : Pt × Pt → ℝ := fun p => (0 : ℕ) * ua p + (1 : ℕ) * ub p + 0 * uc p + fx ep1 with hXc
  set Xm : Fin 3 → Fin 3 → Pt × Pt → ℝ := ![![fun _ => 0, Xa, Xb], ![fun _ => 0, fun _ => 0, Xc],
    ![fun _ => 0, fun _ => 0, fun _ => 0]] with hXm
  set Y : Pt × Pt → Fin 3 → Pt := fun p => ![-(p.1 + p.2), -p.2, (0 : Pt)] with hY
  set c : Fin 3 → Pt := ![c0, c1, (0 : Pt)] with hc
  have he0n : 0 ≤ fx ep0 := le_trans (Real.sqrt_nonneg _) he0
  have he1n : 0 ≤ fx ep1 := le_trans (Real.sqrt_nonneg _) he1
  -- step 1: pointwise
  have hpt : ∀ p ∈ Z ×ˢ Z', unionArea c + ∑ i, teGrad c i (Y p i - c i) - teRem dlo dhi first (fun i j => Xm i j p)
      ≤ unionArea (Y p) := by
    intro p hp
    have h := te_vl_pt hV (c := c) (y := Y p) (dlo := dlo) (dhi := dhi) (first := first)
      (X := fun i j => Xm i j p) ?_ ?_ ?_ ?_
    · have := (abs_le.mp h).1; linarith
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
        Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij <;> simp only [hdlo, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue] <;> first
        | exact fx_pos_iff.mpr hda | exact fx_pos_iff.mpr hdb | exact fx_pos_iff.mpr hdc | exact absurd hij (by decide)
    · intro i j hij t ht
      fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
        Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij
      all_goals first | exact absurd hij (by decide) | skip
      · simp only [hdlo, hdhi, hY, hc, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
        rw [te_edist2_seg c0 (-(p.1 + p.2)) c1 (-p.2) (c1 - c0) p.1 t rfl (by abel)]
        exact hsa p hp t ht
      · simp only [hdlo, hdhi, hY, hc, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
        rw [te_edist2_seg c0 (-(p.1 + p.2)) 0 0 (-c0) (p.1 + p.2) t (by abel) (by abel)]
        exact hsb p hp t ht
      · simp only [hdlo, hdhi, hY, hc, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
        rw [te_edist2_seg c1 (-p.2) 0 0 (-c1) p.2 t (by abel) (by abel)]
        exact hsc p hp t ht
    · intro i j hij hf
      fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
        Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij
      all_goals first | exact absurd hij (by decide) | skip
      all_goals simp only [hfirst, hdhi, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, decide_eq_true_eq] at hf ⊢
      all_goals exact te_useFirst_dhi hf
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
        Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij
      all_goals first | exact absurd hij (by decide) | skip
      · simp only [hXm, hXa, hY, hc, hua, hub, huc, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, Nat.cast_one, Nat.cast_ofNat, one_mul, zero_mul, add_zero, te_fx_add]
        have h0 := te_d0 p.1 p.2 C C' c0
        have h1 := te_d1 p.2 C' c1
        linarith
      · simp only [hXm, hXb, hY, hc, hua, hub, huc, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, Nat.cast_one, one_mul, zero_mul, add_zero,
          sub_zero, te_enorm2_zero]
        have h0 := te_d0 p.1 p.2 C C' c0
        linarith
      · simp only [hXm, hXc, hY, hc, hua, hub, huc, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul,
          add_zero, zero_add, sub_zero, te_enorm2_zero]
        have h1 := te_d1 p.2 C' c1
        linarith
  -- step 2: integrate the lower function
  have hS0 : volume (Z ×ˢ Z') ≠ 0 := by
    rw [Measure.volume_eq_prod (α := Pt) (β := Pt), Measure.prod_prod]; exact mul_ne_zero hZ0 hZ'0
  obtain ⟨p₀, hp₀⟩ := nonempty_of_measure_ne_zero hS0
  have hcY : ∀ i, Continuous fun p : Pt × Pt => Y p i := by
    intro i; fin_cases i <;> simp only [hY, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Fin.isValue] <;> fun_prop
  have hcXm : ∀ i j, Continuous (Xm i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [hXm, hXa, hXb, hXc, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val, Fin.isValue] <;> first | exact continuous_const | fun_prop
  have hcG : Continuous fun p : Pt × Pt => ∑ i, teGrad c i (Y p i - c i) := by
    apply continuous_finset_sum; intro i _; unfold teGrad; have := hcY i; fun_prop
  have hcR : Continuous fun p : Pt × Pt => teRem dlo dhi first (fun i j => Xm i j p) := by
    unfold teRem
    apply continuous_finset_sum; intro i _; apply continuous_finset_sum; intro j _
    split_ifs
    · exact continuous_const.mul ((continuous_Qf _ _ _).comp (hcXm i j))
    · exact continuous_const
  have iG : IntegrableOn (fun p : Pt × Pt => ∑ i, teGrad c i (Y p i - c i)) (Z ×ˢ Z') := hint _ hcG
  have iR : IntegrableOn (fun p : Pt × Pt => teRem dlo dhi first (fun i j => Xm i j p)) (Z ×ˢ Z') := hint _ hcR
  have iCG : IntegrableOn (fun p : Pt × Pt => unionArea c + ∑ i, teGrad c i (Y p i - c i)) (Z ×ˢ Z') :=
    hint _ (continuous_const.add hcG)
  have iL : IntegrableOn (fun p : Pt × Pt =>
      unionArea c + ∑ i, teGrad c i (Y p i - c i) - teRem dlo dhi first (fun i j => Xm i j p)) (Z ×ˢ Z') :=
    hint _ ((continuous_const.add hcG).sub hcR)
  have hmono := setIntegral_mono_on iL hUint (hZm.prod hZ'm) hpt
  have iC : IntegrableOn (fun _ : Pt × Pt => unionArea c) (Z ×ˢ Z') := hint _ continuous_const
  rw [integral_sub iCG iR, integral_add iC iG, setIntegral_const, measureReal_def, hSV,
    smul_eq_mul] at hmono
  -- step 3: the gradient term
  set Dm : Fin 3 → Pt := ![-(C + C') - c0, -C' - c1, 0] with hDm
  set ee : Fin 3 → ℝ := ![fx ep0, fx ep1, 0] with hee
  have hgrad := te_int_grad (μ := volume) (S := Z ×ˢ Z') hint c Y hcY Dm ?_ ee ?_
  rotate_left
  · intro i
    rw [hSV]
    fin_cases i
    · simp only [hY, hc, hDm, Fin.zero_eta, Matrix.cons_val, Fin.isValue]
      constructor
      · rw [show (fun p : Pt × Pt => (-(p.1 + p.2) - c0).1) = fun p : Pt × Pt =>
            ((-1) * p.1.1 + 0 * p.1.2 + ((-1) * p.2.1 + 0 * p.2.2) + -c0.1) from by
          funext p; simp only [Prod.fst_sub, Prod.fst_neg, Prod.fst_add]; ring]
        rw [te_int2_aff hZ0 hZt hZ'0 hZ't hint hZi hZ'i]
        simp only [Prod.fst_sub, Prod.fst_neg, Prod.fst_add]; ring
      · rw [show (fun p : Pt × Pt => (-(p.1 + p.2) - c0).2) = fun p : Pt × Pt =>
            (0 * p.1.1 + (-1) * p.1.2 + (0 * p.2.1 + (-1) * p.2.2) + -c0.2) from by
          funext p; simp only [Prod.snd_sub, Prod.snd_neg, Prod.snd_add]; ring]
        rw [te_int2_aff hZ0 hZt hZ'0 hZ't hint hZi hZ'i]
        simp only [Prod.snd_sub, Prod.snd_neg, Prod.snd_add]; ring
    · simp only [hY, hc, hDm, Fin.mk_one, Matrix.cons_val, Fin.isValue]
      constructor
      · rw [show (fun p : Pt × Pt => (-p.2 - c1).1) = fun p : Pt × Pt =>
            (0 * p.1.1 + 0 * p.1.2 + ((-1) * p.2.1 + 0 * p.2.2) + -c1.1) from by
          funext p; simp only [Prod.fst_sub, Prod.fst_neg]; ring]
        rw [te_int2_aff hZ0 hZt hZ'0 hZ't hint hZi hZ'i]
        simp only [Prod.fst_sub, Prod.fst_neg]; ring
      · rw [show (fun p : Pt × Pt => (-p.2 - c1).2) = fun p : Pt × Pt =>
            (0 * p.1.1 + 0 * p.1.2 + (0 * p.2.1 + (-1) * p.2.2) + -c1.2) from by
          funext p; simp only [Prod.snd_sub, Prod.snd_neg]; ring]
        rw [te_int2_aff hZ0 hZt hZ'0 hZ't hint hZi hZ'i]
        simp only [Prod.snd_sub, Prod.snd_neg]; ring
    · simp only [hY, hc, hDm, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, sub_self, Prod.fst_zero,
        Prod.snd_zero, integral_zero, mul_zero, and_self]
  · intro i
    fin_cases i
    · simp only [hDm, hee, Fin.zero_eta, Matrix.cons_val, Fin.isValue]
      rw [show -(C + C') - c0 = -((C + C') - -c0) by abel, te_enorm2_neg, te_enorm2_sub_eq]; exact he0
    · simp only [hDm, hee, Fin.mk_one, Matrix.cons_val, Fin.isValue]
      rw [show -C' - c1 = -(C' - -c1) by abel, te_enorm2_neg, te_enorm2_sub_eq]; exact he1
    · simp only [hDm, hee, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, te_enorm2_zero, le_refl]
  rw [hSV] at hgrad
  have hee3 : ∑ i, ee i = fx ep0 + fx ep1 := by
    simp only [Fin.sum_univ_three, hee, Fin.isValue, Matrix.cons_val, add_zero]
  rw [hee3] at hgrad
  -- step 4: the remainder
  set S1a : ℝ := ((1 : ℕ) : ℝ) * √mZ + ((2 : ℕ) : ℝ) * √mZ' + 0 * √0 + fx (ep0 + ep1) with hS1a
  set S1b : ℝ := ((1 : ℕ) : ℝ) * √mZ + ((1 : ℕ) : ℝ) * √mZ' + 0 * √0 + fx ep0 with hS1b
  set S1c : ℝ := ((0 : ℕ) : ℝ) * √mZ + ((1 : ℕ) : ℝ) * √mZ' + 0 * √0 + fx ep1 with hS1c
  set S1m : Fin 3 → Fin 3 → ℝ := ![![0, S1a, S1b], ![0, 0, S1c], ![0, 0, 0]] with hS1m
  set S2m : Fin 3 → Fin 3 → ℝ := ![![0, S1a ^ 2, S1b ^ 2], ![0, 0, S1c ^ 2], ![0, 0, 0]] with hS2m
  have hma : ∫ p in Z ×ˢ Z', ua p ^ 2 ≤ mZ * (volume (Z ×ˢ Z')).toReal := by
    simp only [hua]
    simp_rw [te_enorm2_sq']
    rw [te_int2_fst (fun z => sqDist z C), hSV]
    nlinarith
  have hmb : ∫ p in Z ×ˢ Z', ub p ^ 2 ≤ mZ' * (volume (Z ×ˢ Z')).toReal := by
    simp only [hub]
    simp_rw [te_enorm2_sq']
    rw [te_int2_snd (fun z => sqDist z C'), hSV]
    nlinarith
  have hmc : ∫ p in Z ×ˢ Z', uc p ^ 2 ≤ 0 * (volume (Z ×ˢ Z')).toReal := by
    simp only [huc]; simp
  have he01 : 0 ≤ fx (ep0 + ep1) := by rw [te_fx_add]; linarith
  have Ma := te_moments3 hint hSt cua cub cuc hm0 hm'0 le_rfl (Nat.cast_nonneg 1) (Nat.cast_nonneg 2) le_rfl
    he01 hma hmb hmc
  have Mb := te_moments3 hint hSt cua cub cuc hm0 hm'0 le_rfl (Nat.cast_nonneg 1) (Nat.cast_nonneg 1) le_rfl
    he0n hma hmb hmc
  have Mc := te_moments3 hint hSt cua cub cuc hm0 hm'0 le_rfl (Nat.cast_nonneg 0) (Nat.cast_nonneg 1) le_rfl
    he1n hma hmb hmc
  -- d⁻ ≤ d⁺ (at a point of the product, t = 0), hence μ ≥ 0
  have t0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hla := hsa p₀ hp₀ 0 t0
  have hlb := hsb p₀ hp₀ 0 t0
  have hlc := hsc p₀ hp₀ 0 t0
  have hrem := te_int_rem (μ := volume) (S := Z ×ˢ Z') hint dlo dhi first Xm hcXm S1m S2m ?_ ?_ ?_ ?_
  rotate_left
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij <;> simp only [hdlo, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val, Fin.isValue] <;> first
      | exact fx_pos_iff.mpr hda | exact fx_pos_iff.mpr hdb | exact fx_pos_iff.mpr hdc | exact absurd hij (by decide)
  · intro i j hij h2 _
    fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij
    all_goals first | exact absurd hij (by decide) | skip
    all_goals simp only [hdlo, hdhi, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue] at h2 ⊢
    · exact te_mu_nonneg (hla.1.trans hla.2) h2
    · exact te_mu_nonneg (hlb.1.trans hlb.2) h2
    · exact te_mu_nonneg (hlc.1.trans hlc.2) h2
  · intro i j hij _
    fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij
    all_goals first | exact absurd hij (by decide) | skip
    all_goals simp only [hXm, hS1m, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    · exact Ma.1
    · exact Mb.1
    · exact Mc.1
  · intro i j hij _
    fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij
    all_goals first | exact absurd hij (by decide) | skip
    all_goals simp only [hXm, hS2m, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    · exact Ma.2
    · exact Mb.2
    · exact Mc.2
  rw [hSV] at hrem
  -- step 5: the code's remainders
  have hS1a0 : 0 ≤ S1a := by positivity
  have hS1b0 : 0 ≤ S1b := by positivity
  have hS1c0 : 0 ≤ S1c := by positivity
  have ta := te_pair_term hAS hra hS1a0 (sq_nonneg S1a) (by rw [te_momentsX2]; exact te_S1_le hsqa hsqb)
    (by rw [te_momentsX2]; exact te_S2_le hS1a0 (te_S1_le hsqa hsqb))
  have tb := te_pair_term hAS hrb hS1b0 (sq_nonneg S1b) (by rw [te_momentsX2]; exact te_S1_le hsqa hsqb)
    (by rw [te_momentsX2]; exact te_S2_le hS1b0 (te_S1_le hsqa hsqb))
  have tc := te_pair_term hAS hrc hS1c0 (sq_nonneg S1c) (by rw [te_momentsX2]; exact te_S1_le hsqa hsqb)
    (by rw [te_momentsX2]; exact te_S2_le hS1c0 (te_S1_le hsqa hsqb))
  have hsum : (∑ i, ∑ j, if i < j ∧ dlo i j < 2 then
      2 * pairRem (dlo i j) (dhi i j) (first i j) (S1m i j) (S2m i j) else 0) ≤ fx ra + fx rb + fx rc := by
    simp only [Fin.sum_univ_three, hdlo, hdhi, hfirst, hS1m, hS2m, Fin.isValue, Matrix.cons_val]
    simp (config := { decide := true }) only [Fin.reduceLT, lt_self_iff_false, false_and, true_and, if_false,
      add_zero, zero_add]
    linarith
  -- step 6: combine
  have hVV : 0 ≤ (volume Z).toReal * (volume Z').toReal := (mul_pos hVp hV'p).le
  have hgl := (abs_le.mp hgrad).1
  have hfin := mul_le_mul_of_nonneg_right hsum hVV
  have hUV := mul_le_mul_of_nonneg_right hU hVV
  nlinarith


/-! ## Layer 2: the triple entry -/

lemma te_S1_le3 {wa wb wc : ℕ} {sqa sqb sqc e : ℤ} {ma mb mc : ℝ} (ha : √ma ≤ fx sqa) (hb : √mb ≤ fx sqb)
    (hc : √mc ≤ fx sqc) :
    (wa : ℝ) * √ma + (wb : ℝ) * √mb + (wc : ℝ) * √mc + fx e ≤ fx (e + wa * sqa + wb * sqb + wc * sqc) := by
  rw [te_fx_add, te_fx_add, te_fx_add, te_fx_natMul, te_fx_natMul, te_fx_natMul]
  have h1 := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg wa)
  have h2 := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg wb)
  have h3 := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg wc)
  linarith

/-- integral over `A × (B × C)` of a separated function -/
lemma te_int3_sep {A B C : Set Pt} (hint : ∀ F : Pt × (Pt × Pt) → ℝ, Continuous F → IntegrableOn F (A ×ˢ (B ×ˢ C)))
    (hSt : volume (A ×ˢ (B ×ˢ C)) ≠ ⊤) {f g h : Pt → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) (k : ℝ) :
    ∫ p in A ×ˢ (B ×ˢ C), (f p.1 + g p.2.1 + h p.2.2 + k) =
      (∫ z in A, f z) * ((volume B).toReal * (volume C).toReal) +
        (volume A).toReal * ((∫ z in B, g z) * (volume C).toReal) +
        (volume A).toReal * ((volume B).toReal * ∫ z in C, h z) +
        k * ((volume A).toReal * (volume B).toReal * (volume C).toReal) := by
  have i1 : IntegrableOn (fun p : Pt × (Pt × Pt) => f p.1) (A ×ˢ (B ×ˢ C)) := hint _ (hf.comp continuous_fst)
  have i2 : IntegrableOn (fun p : Pt × (Pt × Pt) => g p.2.1) (A ×ˢ (B ×ˢ C)) :=
    hint _ (hg.comp (continuous_fst.comp continuous_snd))
  have i3 : IntegrableOn (fun p : Pt × (Pt × Pt) => h p.2.2) (A ×ˢ (B ×ˢ C)) :=
    hint _ (hh.comp (continuous_snd.comp continuous_snd))
  have i12 : IntegrableOn (fun p : Pt × (Pt × Pt) => f p.1 + g p.2.1) (A ×ˢ (B ×ˢ C)) := i1.add i2
  have i123 : IntegrableOn (fun p : Pt × (Pt × Pt) => f p.1 + g p.2.1 + h p.2.2) (A ×ˢ (B ×ˢ C)) := i12.add i3
  rw [integral_add i123 (integrableOn_const hSt), integral_add i12 i3, integral_add i1 i2, te_int3_fst,
    te_int3_mid, te_int3_lst, setIntegral_const, measureReal_def, te_vol3, smul_eq_mul, mul_comm k]

/-- integral over `A × (B × C)` of an affine function of the six coordinates -/
lemma te_int3_aff {A B C : Set Pt} (hA0 : volume A ≠ 0) (hAt : volume A ≠ ⊤) (hB0 : volume B ≠ 0)
    (hBt : volume B ≠ ⊤) (hC0 : volume C ≠ 0) (hCt : volume C ≠ ⊤)
    (hint : ∀ F : Pt × (Pt × Pt) → ℝ, Continuous F → IntegrableOn F (A ×ˢ (B ×ˢ C)))
    (hAi : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f A) (hBi : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f B)
    (hCi : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f C) (a b a' b' a'' b'' k : ℝ) :
    ∫ p in A ×ˢ (B ×ˢ C), (a * p.1.1 + b * p.1.2 + (a' * p.2.1.1 + b' * p.2.1.2) +
        (a'' * p.2.2.1 + b'' * p.2.2.2) + k) =
      (volume A).toReal * (volume B).toReal * (volume C).toReal *
        (a * (cen A).1 + b * (cen A).2 + (a' * (cen B).1 + b' * (cen B).2) +
          (a'' * (cen C).1 + b'' * (cen C).2) + k) := by
  have hSt : volume (A ×ˢ (B ×ˢ C)) ≠ ⊤ := by
    rw [Measure.volume_eq_prod (α := Pt) (β := Pt × Pt), Measure.prod_prod,
      Measure.volume_eq_prod (α := Pt) (β := Pt), Measure.prod_prod]
    exact ENNReal.mul_ne_top hAt (ENNReal.mul_ne_top hBt hCt)
  rw [te_int3_sep (f := fun z : Pt => a * z.1 + b * z.2) (g := fun z : Pt => a' * z.1 + b' * z.2)
    (h := fun z : Pt => a'' * z.1 + b'' * z.2) hint hSt (by fun_prop) (by fun_prop) (by fun_prop) k]
  obtain ⟨h1, h2⟩ := te_cen_mul hA0 hAt
  obtain ⟨h1', h2'⟩ := te_cen_mul hB0 hBt
  obtain ⟨h1'', h2''⟩ := te_cen_mul hC0 hCt
  have iA1 : IntegrableOn (fun z : Pt => a * z.1) A := hAi _ (by fun_prop)
  have iA2 : IntegrableOn (fun z : Pt => b * z.2) A := hAi _ (by fun_prop)
  have iB1 : IntegrableOn (fun z : Pt => a' * z.1) B := hBi _ (by fun_prop)
  have iB2 : IntegrableOn (fun z : Pt => b' * z.2) B := hBi _ (by fun_prop)
  have iC1 : IntegrableOn (fun z : Pt => a'' * z.1) C := hCi _ (by fun_prop)
  have iC2 : IntegrableOn (fun z : Pt => b'' * z.2) C := hCi _ (by fun_prop)
  rw [integral_add iA1 iA2, integral_add iB1 iB2, integral_add iC1 iC2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, h1, h2, h1', h2', h1'', h2'']
  ring


set_option maxHeartbeats 16000000 in
/-- The vertex lemma integrated over `A × B × C` for the configuration `(-(z_a + z_b), -z_b, 0, z_c)` at the expansion
point `(c0, c1, 0, c3)`, upper side, with the code's six pair remainders and moment data. -/
theorem te_tri_core (hV : VertexLemmaSeg) (hAS : AsinTSound) {A B C : Set Pt}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hCm : MeasurableSet C)
    (hint : ∀ f : Pt × (Pt × Pt) → ℝ, Continuous f → IntegrableOn f (A ×ˢ (B ×ˢ C)))
    (hAi : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f A) (hBi : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f B)
    (hCi : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f C)
    (hA0 : volume A ≠ 0) (hAt : volume A ≠ ⊤) (hB0 : volume B ≠ 0) (hBt : volume B ≠ ⊤)
    (hC0 : volume C ≠ 0) (hCt : volume C ≠ ⊤)
    {mA mB mC : ℝ} (hmA0 : 0 ≤ mA) (hmB0 : 0 ≤ mB) (hmC0 : 0 ≤ mC)
    (hmA : ∫ z in A, sqDist z (cen A) ≤ mA * (volume A).toReal)
    (hmB : ∫ z in B, sqDist z (cen B) ≤ mB * (volume B).toReal)
    (hmC : ∫ z in C, sqDist z (cen C) ≤ mC * (volume C).toReal)
    {sqa sqb sqc : ℤ} (hsqa : √mA ≤ fx sqa) (hsqb : √mB ≤ fx sqb) (hsqc : √mC ≤ fx sqc)
    {c0 c1 c3 : Pt} {ep0 ep1 ep3 : ℤ} (he0 : edist2 (cen A + cen B) (-c0) ≤ fx ep0)
    (he1 : edist2 (cen B) (-c1) ≤ fx ep1) (he3 : edist2 (cen C) c3 ≤ fx ep3)
    {U : ℝ} (hU : unionArea ![c0, c1, (0 : Pt), c3] ≤ U)
    {dn01 dx01 dn02 dx02 dn03 dx03 dn12 dx12 dn13 dx13 dn23 dx23 r01 r02 r03 r12 r13 r23 : ℤ}
    (hr01 : W3C.lvPairT W3C.mkAsinTab dn01 dx01 (W3C.momentsX [1, 2, 0] [sqa, sqb, sqc] (ep0 + ep1)).1
      (W3C.momentsX [1, 2, 0] [sqa, sqb, sqc] (ep0 + ep1)).2 = some r01)
    (hr02 : W3C.lvPairT W3C.mkAsinTab dn02 dx02 (W3C.momentsX [1, 1, 0] [sqa, sqb, sqc] ep0).1
      (W3C.momentsX [1, 1, 0] [sqa, sqb, sqc] ep0).2 = some r02)
    (hr03 : W3C.lvPairT W3C.mkAsinTab dn03 dx03 (W3C.momentsX [1, 1, 1] [sqa, sqb, sqc] (ep0 + ep3)).1
      (W3C.momentsX [1, 1, 1] [sqa, sqb, sqc] (ep0 + ep3)).2 = some r03)
    (hr12 : W3C.lvPairT W3C.mkAsinTab dn12 dx12 (W3C.momentsX [0, 1, 0] [sqa, sqb, sqc] ep1).1
      (W3C.momentsX [0, 1, 0] [sqa, sqb, sqc] ep1).2 = some r12)
    (hr13 : W3C.lvPairT W3C.mkAsinTab dn13 dx13 (W3C.momentsX [0, 1, 1] [sqa, sqb, sqc] (ep1 + ep3)).1
      (W3C.momentsX [0, 1, 1] [sqa, sqb, sqc] (ep1 + ep3)).2 = some r13)
    (hr23 : W3C.lvPairT W3C.mkAsinTab dn23 dx23 (W3C.momentsX [0, 0, 1] [sqa, sqb, sqc] ep3).1
      (W3C.momentsX [0, 0, 1] [sqa, sqb, sqc] ep3).2 = some r23)
    (hs01 : ∀ p ∈ A ×ˢ (B ×ˢ C), ∀ t ∈ Icc (0 : ℝ) 1,
      fx dn01 ≤ enorm2 ((c1 - c0) + t • (p.1 - (c1 - c0))) ∧ enorm2 ((c1 - c0) + t • (p.1 - (c1 - c0))) ≤ fx dx01)
    (hs02 : ∀ p ∈ A ×ˢ (B ×ˢ C), ∀ t ∈ Icc (0 : ℝ) 1,
      fx dn02 ≤ enorm2 (-c0 + t • ((p.1 + p.2.1) - -c0)) ∧ enorm2 (-c0 + t • ((p.1 + p.2.1) - -c0)) ≤ fx dx02)
    (hs03 : ∀ p ∈ A ×ˢ (B ×ˢ C), ∀ t ∈ Icc (0 : ℝ) 1,
      fx dn03 ≤ enorm2 ((c3 - c0) + t • ((p.2.2 + (p.1 + p.2.1)) - (c3 - c0))) ∧
        enorm2 ((c3 - c0) + t • ((p.2.2 + (p.1 + p.2.1)) - (c3 - c0))) ≤ fx dx03)
    (hs12 : ∀ p ∈ A ×ˢ (B ×ˢ C), ∀ t ∈ Icc (0 : ℝ) 1,
      fx dn12 ≤ enorm2 (-c1 + t • (p.2.1 - -c1)) ∧ enorm2 (-c1 + t • (p.2.1 - -c1)) ≤ fx dx12)
    (hs13 : ∀ p ∈ A ×ˢ (B ×ˢ C), ∀ t ∈ Icc (0 : ℝ) 1,
      fx dn13 ≤ enorm2 ((c3 - c1) + t • ((p.2.2 + p.2.1) - (c3 - c1))) ∧
        enorm2 ((c3 - c1) + t • ((p.2.2 + p.2.1) - (c3 - c1))) ≤ fx dx13)
    (hs23 : ∀ p ∈ A ×ˢ (B ×ˢ C), ∀ t ∈ Icc (0 : ℝ) 1,
      fx dn23 ≤ enorm2 (c3 + t • (p.2.2 - c3)) ∧ enorm2 (c3 + t • (p.2.2 - c3)) ≤ fx dx23)
    {F H : Pt × (Pt × Pt) → ℝ} {L : ℝ} (hF0 : ∀ p, 0 ≤ F p)
    (hFH : ∀ p ∈ A ×ˢ (B ×ˢ C), F p ≤ unionArea ![-(p.1 + p.2.1), -p.2.1, (0 : Pt), p.2.2] - H p)
    (hHi : IntegrableOn H (A ×ˢ (B ×ˢ C)))
    (hH : L * ((volume A).toReal * (volume B).toReal * (volume C).toReal) ≤ ∫ p in A ×ˢ (B ×ˢ C), H p) :
    ∫ p in A ×ˢ (B ×ˢ C), F p ≤
      (U + 2 * (fx ep0 + fx ep1 + fx ep3) + (fx r01 + fx r02 + fx r03 + fx r12 + fx r13 + fx r23) - L) *
        ((volume A).toReal * (volume B).toReal * (volume C).toReal) := by
  have hVA : 0 < (volume A).toReal := ENNReal.toReal_pos hA0 hAt
  have hVB : 0 < (volume B).toReal := ENNReal.toReal_pos hB0 hBt
  have hVC : 0 < (volume C).toReal := ENNReal.toReal_pos hC0 hCt
  have hSV : (volume (A ×ˢ (B ×ˢ C))).toReal = (volume A).toReal * (volume B).toReal * (volume C).toReal :=
    te_vol3 A B C
  have hSt : volume (A ×ˢ (B ×ˢ C)) ≠ ⊤ := by
    rw [Measure.volume_eq_prod (α := Pt) (β := Pt × Pt), Measure.prod_prod,
      Measure.volume_eq_prod (α := Pt) (β := Pt), Measure.prod_prod]
    exact ENNReal.mul_ne_top hAt (ENNReal.mul_ne_top hBt hCt)
  have hSm : MeasurableSet (A ×ˢ (B ×ˢ C)) := hAm.prod (hBm.prod hCm)
  set CA := cen A with hCAdef
  set CB := cen B with hCBdef
  set CC := cen C with hCCdef
  obtain ⟨hd01, -, -⟩ := te_lvPairT_spec hAS hr01
  obtain ⟨hd02, -, -⟩ := te_lvPairT_spec hAS hr02
  obtain ⟨hd03, -, -⟩ := te_lvPairT_spec hAS hr03
  obtain ⟨hd12, -, -⟩ := te_lvPairT_spec hAS hr12
  obtain ⟨hd13, -, -⟩ := te_lvPairT_spec hAS hr13
  obtain ⟨hd23, -, -⟩ := te_lvPairT_spec hAS hr23
  -- the data of the vertex lemma
  set dlo : Fin 4 → Fin 4 → ℝ := ![![0, fx dn01, fx dn02, fx dn03], ![0, 0, fx dn12, fx dn13],
    ![0, 0, 0, fx dn23], ![0, 0, 0, 0]] with hdlo
  set dhi : Fin 4 → Fin 4 → ℝ := ![![0, fx dx01, fx dx02, fx dx03], ![0, 0, fx dx12, fx dx13],
    ![0, 0, 0, fx dx23], ![0, 0, 0, 0]] with hdhi
  set first : Fin 4 → Fin 4 → Bool := ![![false, decide (W2C.useFirstOf dx01), decide (W2C.useFirstOf dx02),
    decide (W2C.useFirstOf dx03)], ![false, false, decide (W2C.useFirstOf dx12), decide (W2C.useFirstOf dx13)],
    ![false, false, false, decide (W2C.useFirstOf dx23)], ![false, false, false, false]] with hfirst
  set ua : Pt × (Pt × Pt) → ℝ := fun p => enorm2 (p.1 - CA) with hua
  set ub : Pt × (Pt × Pt) → ℝ := fun p => enorm2 (p.2.1 - CB) with hub
  set uc : Pt × (Pt × Pt) → ℝ := fun p => enorm2 (p.2.2 - CC) with huc
  have cua : Continuous ua := tp_continuous_enorm2.comp (continuous_fst.sub continuous_const)
  have cub : Continuous ub := tp_continuous_enorm2.comp ((continuous_fst.comp continuous_snd).sub continuous_const)
  have cuc : Continuous uc := tp_continuous_enorm2.comp ((continuous_snd.comp continuous_snd).sub continuous_const)
  set X01 : Pt × (Pt × Pt) → ℝ := fun p => (1 : ℕ) * ua p + (2 : ℕ) * ub p + (0 : ℕ) * uc p + fx (ep0 + ep1)
    with hX01
  set X02 : Pt × (Pt × Pt) → ℝ := fun p => (1 : ℕ) * ua p + (1 : ℕ) * ub p + (0 : ℕ) * uc p + fx ep0 with hX02
  set X03 : Pt × (Pt × Pt) → ℝ := fun p => (1 : ℕ) * ua p + (1 : ℕ) * ub p + (1 : ℕ) * uc p + fx (ep0 + ep3)
    with hX03
  set X12 : Pt × (Pt × Pt) → ℝ := fun p => (0 : ℕ) * ua p + (1 : ℕ) * ub p + (0 : ℕ) * uc p + fx ep1 with hX12
  set X13 : Pt × (Pt × Pt) → ℝ := fun p => (0 : ℕ) * ua p + (1 : ℕ) * ub p + (1 : ℕ) * uc p + fx (ep1 + ep3)
    with hX13
  set X23 : Pt × (Pt × Pt) → ℝ := fun p => (0 : ℕ) * ua p + (0 : ℕ) * ub p + (1 : ℕ) * uc p + fx ep3 with hX23
  set Xm : Fin 4 → Fin 4 → Pt × (Pt × Pt) → ℝ := ![![fun _ => 0, X01, X02, X03], ![fun _ => 0, fun _ => 0, X12, X13],
    ![fun _ => 0, fun _ => 0, fun _ => 0, X23], ![fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0]] with hXm
  set Y : Pt × (Pt × Pt) → Fin 4 → Pt := fun p => ![-(p.1 + p.2.1), -p.2.1, (0 : Pt), p.2.2] with hY
  set c : Fin 4 → Pt := ![c0, c1, (0 : Pt), c3] with hc
  have he0n : 0 ≤ fx ep0 := le_trans (Real.sqrt_nonneg _) he0
  have he1n : 0 ≤ fx ep1 := le_trans (Real.sqrt_nonneg _) he1
  have he3n : 0 ≤ fx ep3 := le_trans (Real.sqrt_nonneg _) he3
  -- step 1: pointwise
  have hpt : ∀ p ∈ A ×ˢ (B ×ˢ C), unionArea (Y p) ≤
      unionArea c + ∑ i, teGrad c i (Y p i - c i) + teRem dlo dhi first (fun i j => Xm i j p) := by
    intro p hp
    have h := te_vl_pt hV (c := c) (y := Y p) (dlo := dlo) (dhi := dhi) (first := first)
      (X := fun i j => Xm i j p) ?_ ?_ ?_ ?_
    · have := (abs_le.mp h).2; linarith
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
        Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij <;> simp only [hdlo, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val, Fin.isValue] <;> first
        | exact fx_pos_iff.mpr hd01 | exact fx_pos_iff.mpr hd02 | exact fx_pos_iff.mpr hd03
        | exact fx_pos_iff.mpr hd12 | exact fx_pos_iff.mpr hd13 | exact fx_pos_iff.mpr hd23
        | exact absurd hij (by decide)
    · intro i j hij t ht
      fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
        Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij
      all_goals first | exact absurd hij (by decide) | skip
      all_goals simp only [hdlo, hdhi, hY, hc, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      · rw [te_edist2_seg c0 (-(p.1 + p.2.1)) c1 (-p.2.1) (c1 - c0) p.1 t rfl (by abel)]
        exact hs01 p hp t ht
      · rw [te_edist2_seg c0 (-(p.1 + p.2.1)) 0 0 (-c0) (p.1 + p.2.1) t (by abel) (by abel)]
        exact hs02 p hp t ht
      · rw [te_edist2_seg c0 (-(p.1 + p.2.1)) c3 p.2.2 (c3 - c0) (p.2.2 + (p.1 + p.2.1)) t rfl (by abel)]
        exact hs03 p hp t ht
      · rw [te_edist2_seg c1 (-p.2.1) 0 0 (-c1) p.2.1 t (by abel) (by abel)]
        exact hs12 p hp t ht
      · rw [te_edist2_seg c1 (-p.2.1) c3 p.2.2 (c3 - c1) (p.2.2 + p.2.1) t rfl (by abel)]
        exact hs13 p hp t ht
      · rw [te_edist2_seg 0 0 c3 p.2.2 c3 p.2.2 t (by abel) (by abel)]
        exact hs23 p hp t ht
    · intro i j hij hf
      fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
        Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij
      all_goals first | exact absurd hij (by decide) | skip
      all_goals simp only [hfirst, hdhi, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue,
          decide_eq_true_eq] at hf ⊢
      all_goals exact te_useFirst_dhi hf
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
        Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij
      all_goals first | exact absurd hij (by decide) | skip
      all_goals simp only [hXm, hX01, hX02, hX03, hX12, hX13, hX23, hY, hc, hua, hub, huc, Fin.zero_eta, Fin.mk_one,
        Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero, one_mul,
        zero_mul, add_zero, zero_add, sub_zero, te_enorm2_zero, te_fx_add]
      · have h0 := te_d0 p.1 p.2.1 CA CB c0
        have h1 := te_d1 p.2.1 CB c1
        linarith
      · have h0 := te_d0 p.1 p.2.1 CA CB c0
        linarith
      · have h0 := te_d0 p.1 p.2.1 CA CB c0
        have h3 := te_d3 p.2.2 CC c3
        linarith
      · have h1 := te_d1 p.2.1 CB c1
        linarith
      · have h1 := te_d1 p.2.1 CB c1
        have h3 := te_d3 p.2.2 CC c3
        linarith
      · have h3 := te_d3 p.2.2 CC c3
        linarith
  -- step 2: integrate the upper function
  have hS0 : volume (A ×ˢ (B ×ˢ C)) ≠ 0 := by
    rw [Measure.volume_eq_prod (α := Pt) (β := Pt × Pt), Measure.prod_prod,
      Measure.volume_eq_prod (α := Pt) (β := Pt), Measure.prod_prod]
    exact mul_ne_zero hA0 (mul_ne_zero hB0 hC0)
  obtain ⟨p₀, hp₀⟩ := nonempty_of_measure_ne_zero hS0
  have hcY : ∀ i, Continuous fun p : Pt × (Pt × Pt) => Y p i := by
    intro i; fin_cases i <;> simp only [hY, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Fin.isValue] <;> fun_prop
  have hcXm : ∀ i j, Continuous (Xm i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [hXm, hX01, hX02, hX03, hX12, hX13, hX23, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val, Fin.isValue] <;> first | exact continuous_const | fun_prop
  have hcG : Continuous fun p : Pt × (Pt × Pt) => ∑ i, teGrad c i (Y p i - c i) := by
    apply continuous_finset_sum; intro i _; unfold teGrad; have := hcY i; fun_prop
  have hcR : Continuous fun p : Pt × (Pt × Pt) => teRem dlo dhi first (fun i j => Xm i j p) := by
    unfold teRem
    apply continuous_finset_sum; intro i _; apply continuous_finset_sum; intro j _
    split_ifs
    · exact continuous_const.mul ((continuous_Qf _ _ _).comp (hcXm i j))
    · exact continuous_const
  have iC : IntegrableOn (fun _ : Pt × (Pt × Pt) => U) (A ×ˢ (B ×ˢ C)) := hint _ continuous_const
  have iG : IntegrableOn (fun p : Pt × (Pt × Pt) => ∑ i, teGrad c i (Y p i - c i)) (A ×ˢ (B ×ˢ C)) := hint _ hcG
  have iR : IntegrableOn (fun p : Pt × (Pt × Pt) => teRem dlo dhi first (fun i j => Xm i j p))
      (A ×ˢ (B ×ˢ C)) := hint _ hcR
  have iCG : IntegrableOn (fun p : Pt × (Pt × Pt) => U + ∑ i, teGrad c i (Y p i - c i)) (A ×ˢ (B ×ˢ C)) :=
    hint _ (continuous_const.add hcG)
  have iCGR : IntegrableOn (fun p : Pt × (Pt × Pt) =>
      U + ∑ i, teGrad c i (Y p i - c i) + teRem dlo dhi first (fun i j => Xm i j p)) (A ×ˢ (B ×ˢ C)) :=
    hint _ ((continuous_const.add hcG).add hcR)
  have iUp : IntegrableOn (fun p : Pt × (Pt × Pt) =>
      U + ∑ i, teGrad c i (Y p i - c i) + teRem dlo dhi first (fun i j => Xm i j p) - H p) (A ×ˢ (B ×ˢ C)) :=
    iCGR.sub hHi
  have hmono : ∫ p in A ×ˢ (B ×ˢ C), F p ≤ ∫ p in A ×ˢ (B ×ˢ C),
      (U + ∑ i, teGrad c i (Y p i - c i) + teRem dlo dhi first (fun i j => Xm i j p) - H p) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => hF0 p) iUp ?_
    refine (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun p hp => ?_)
    have h1 := hFH p hp
    have h2 := hpt p hp
    linarith
  rw [integral_sub iCGR hHi, integral_add iCG iR, integral_add iC iG, setIntegral_const, measureReal_def, hSV,
    smul_eq_mul] at hmono
  -- step 3: the gradient term
  set Dm : Fin 4 → Pt := ![-(CA + CB) - c0, -CB - c1, 0, CC - c3] with hDm
  set ee : Fin 4 → ℝ := ![fx ep0, fx ep1, 0, fx ep3] with hee
  have hgrad := te_int_grad (μ := volume) (S := A ×ˢ (B ×ˢ C)) hint c Y hcY Dm ?_ ee ?_
  rotate_left
  · intro i
    rw [hSV]
    fin_cases i
    · simp only [hY, hc, hDm, Fin.zero_eta, Matrix.cons_val, Fin.isValue]
      constructor
      · rw [show (fun p : Pt × (Pt × Pt) => (-(p.1 + p.2.1) - c0).1) = fun p : Pt × (Pt × Pt) =>
            ((-1) * p.1.1 + 0 * p.1.2 + ((-1) * p.2.1.1 + 0 * p.2.1.2) + (0 * p.2.2.1 + 0 * p.2.2.2) + -c0.1) from by
          funext p; simp only [Prod.fst_sub, Prod.fst_neg, Prod.fst_add]; ring]
        rw [te_int3_aff hA0 hAt hB0 hBt hC0 hCt hint hAi hBi hCi]
        simp only [Prod.fst_sub, Prod.fst_neg, Prod.fst_add]; ring
      · rw [show (fun p : Pt × (Pt × Pt) => (-(p.1 + p.2.1) - c0).2) = fun p : Pt × (Pt × Pt) =>
            (0 * p.1.1 + (-1) * p.1.2 + (0 * p.2.1.1 + (-1) * p.2.1.2) + (0 * p.2.2.1 + 0 * p.2.2.2) + -c0.2) from by
          funext p; simp only [Prod.snd_sub, Prod.snd_neg, Prod.snd_add]; ring]
        rw [te_int3_aff hA0 hAt hB0 hBt hC0 hCt hint hAi hBi hCi]
        simp only [Prod.snd_sub, Prod.snd_neg, Prod.snd_add]; ring
    · simp only [hY, hc, hDm, Fin.mk_one, Matrix.cons_val, Fin.isValue]
      constructor
      · rw [show (fun p : Pt × (Pt × Pt) => (-p.2.1 - c1).1) = fun p : Pt × (Pt × Pt) =>
            (0 * p.1.1 + 0 * p.1.2 + ((-1) * p.2.1.1 + 0 * p.2.1.2) + (0 * p.2.2.1 + 0 * p.2.2.2) + -c1.1) from by
          funext p; simp only [Prod.fst_sub, Prod.fst_neg]; ring]
        rw [te_int3_aff hA0 hAt hB0 hBt hC0 hCt hint hAi hBi hCi]
        simp only [Prod.fst_sub, Prod.fst_neg]; ring
      · rw [show (fun p : Pt × (Pt × Pt) => (-p.2.1 - c1).2) = fun p : Pt × (Pt × Pt) =>
            (0 * p.1.1 + 0 * p.1.2 + (0 * p.2.1.1 + (-1) * p.2.1.2) + (0 * p.2.2.1 + 0 * p.2.2.2) + -c1.2) from by
          funext p; simp only [Prod.snd_sub, Prod.snd_neg]; ring]
        rw [te_int3_aff hA0 hAt hB0 hBt hC0 hCt hint hAi hBi hCi]
        simp only [Prod.snd_sub, Prod.snd_neg]; ring
    · simp only [hY, hc, hDm, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, sub_self, Prod.fst_zero,
        Prod.snd_zero, integral_zero, mul_zero, and_self]
    · simp only [hY, hc, hDm, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      constructor
      · rw [show (fun p : Pt × (Pt × Pt) => (p.2.2 - c3).1) = fun p : Pt × (Pt × Pt) =>
            (0 * p.1.1 + 0 * p.1.2 + (0 * p.2.1.1 + 0 * p.2.1.2) + (1 * p.2.2.1 + 0 * p.2.2.2) + -c3.1) from by
          funext p; simp only [Prod.fst_sub]; ring]
        rw [te_int3_aff hA0 hAt hB0 hBt hC0 hCt hint hAi hBi hCi]
        simp only [Prod.fst_sub]; ring
      · rw [show (fun p : Pt × (Pt × Pt) => (p.2.2 - c3).2) = fun p : Pt × (Pt × Pt) =>
            (0 * p.1.1 + 0 * p.1.2 + (0 * p.2.1.1 + 0 * p.2.1.2) + (0 * p.2.2.1 + 1 * p.2.2.2) + -c3.2) from by
          funext p; simp only [Prod.snd_sub]; ring]
        rw [te_int3_aff hA0 hAt hB0 hBt hC0 hCt hint hAi hBi hCi]
        simp only [Prod.snd_sub]; ring
  · intro i
    fin_cases i
    · simp only [hDm, hee, Fin.zero_eta, Matrix.cons_val, Fin.isValue]
      rw [show -(CA + CB) - c0 = -((CA + CB) - -c0) by abel, te_enorm2_neg, te_enorm2_sub_eq]; exact he0
    · simp only [hDm, hee, Fin.mk_one, Matrix.cons_val, Fin.isValue]
      rw [show -CB - c1 = -(CB - -c1) by abel, te_enorm2_neg, te_enorm2_sub_eq]; exact he1
    · simp only [hDm, hee, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue, te_enorm2_zero, le_refl]
    · simp only [hDm, hee, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      rw [te_enorm2_sub_eq]; exact he3
  rw [hSV] at hgrad
  have hee4 : ∑ i, ee i = fx ep0 + fx ep1 + fx ep3 := by
    simp only [Fin.sum_univ_four, hee, Fin.isValue, Matrix.cons_val, add_zero]
  rw [hee4] at hgrad
  -- step 4: the remainder
  set S01 : ℝ := ((1 : ℕ) : ℝ) * √mA + ((2 : ℕ) : ℝ) * √mB + ((0 : ℕ) : ℝ) * √mC + fx (ep0 + ep1) with hS01
  set S02 : ℝ := ((1 : ℕ) : ℝ) * √mA + ((1 : ℕ) : ℝ) * √mB + ((0 : ℕ) : ℝ) * √mC + fx ep0 with hS02
  set S03 : ℝ := ((1 : ℕ) : ℝ) * √mA + ((1 : ℕ) : ℝ) * √mB + ((1 : ℕ) : ℝ) * √mC + fx (ep0 + ep3) with hS03
  set S12 : ℝ := ((0 : ℕ) : ℝ) * √mA + ((1 : ℕ) : ℝ) * √mB + ((0 : ℕ) : ℝ) * √mC + fx ep1 with hS12
  set S13 : ℝ := ((0 : ℕ) : ℝ) * √mA + ((1 : ℕ) : ℝ) * √mB + ((1 : ℕ) : ℝ) * √mC + fx (ep1 + ep3) with hS13
  set S23 : ℝ := ((0 : ℕ) : ℝ) * √mA + ((0 : ℕ) : ℝ) * √mB + ((1 : ℕ) : ℝ) * √mC + fx ep3 with hS23
  set S1m : Fin 4 → Fin 4 → ℝ := ![![0, S01, S02, S03], ![0, 0, S12, S13], ![0, 0, 0, S23], ![0, 0, 0, 0]] with hS1m
  set S2m : Fin 4 → Fin 4 → ℝ := ![![0, S01 ^ 2, S02 ^ 2, S03 ^ 2], ![0, 0, S12 ^ 2, S13 ^ 2], ![0, 0, 0, S23 ^ 2],
    ![0, 0, 0, 0]] with hS2m
  have hma : ∫ p in A ×ˢ (B ×ˢ C), ua p ^ 2 ≤ mA * (volume (A ×ˢ (B ×ˢ C))).toReal := by
    simp only [hua]
    simp_rw [te_enorm2_sq']
    rw [te_int3_fst (fun z => sqDist z CA), hSV]
    have := mul_le_mul_of_nonneg_right hmA (mul_pos hVB hVC).le
    nlinarith
  have hmb : ∫ p in A ×ˢ (B ×ˢ C), ub p ^ 2 ≤ mB * (volume (A ×ˢ (B ×ˢ C))).toReal := by
    simp only [hub]
    simp_rw [te_enorm2_sq']
    rw [te_int3_mid (fun z => sqDist z CB), hSV]
    have := mul_le_mul_of_nonneg_right hmB hVC.le
    have := mul_le_mul_of_nonneg_left this hVA.le
    nlinarith
  have hmc : ∫ p in A ×ˢ (B ×ˢ C), uc p ^ 2 ≤ mC * (volume (A ×ˢ (B ×ˢ C))).toReal := by
    simp only [huc]
    simp_rw [te_enorm2_sq']
    rw [te_int3_lst (fun z => sqDist z CC), hSV]
    have := mul_le_mul_of_nonneg_left hmC hVB.le
    have := mul_le_mul_of_nonneg_left this hVA.le
    nlinarith
  have he01 : 0 ≤ fx (ep0 + ep1) := by rw [te_fx_add]; linarith
  have he03 : 0 ≤ fx (ep0 + ep3) := by rw [te_fx_add]; linarith
  have he13 : 0 ≤ fx (ep1 + ep3) := by rw [te_fx_add]; linarith
  have M01 := te_moments3 hint hSt cua cub cuc hmA0 hmB0 hmC0 (Nat.cast_nonneg 1) (Nat.cast_nonneg 2)
    (Nat.cast_nonneg 0) he01 hma hmb hmc
  have M02 := te_moments3 hint hSt cua cub cuc hmA0 hmB0 hmC0 (Nat.cast_nonneg 1) (Nat.cast_nonneg 1)
    (Nat.cast_nonneg 0) he0n hma hmb hmc
  have M03 := te_moments3 hint hSt cua cub cuc hmA0 hmB0 hmC0 (Nat.cast_nonneg 1) (Nat.cast_nonneg 1)
    (Nat.cast_nonneg 1) he03 hma hmb hmc
  have M12 := te_moments3 hint hSt cua cub cuc hmA0 hmB0 hmC0 (Nat.cast_nonneg 0) (Nat.cast_nonneg 1)
    (Nat.cast_nonneg 0) he1n hma hmb hmc
  have M13 := te_moments3 hint hSt cua cub cuc hmA0 hmB0 hmC0 (Nat.cast_nonneg 0) (Nat.cast_nonneg 1)
    (Nat.cast_nonneg 1) he13 hma hmb hmc
  have M23 := te_moments3 hint hSt cua cub cuc hmA0 hmB0 hmC0 (Nat.cast_nonneg 0) (Nat.cast_nonneg 0)
    (Nat.cast_nonneg 1) he3n hma hmb hmc
  have t0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hl01 := hs01 p₀ hp₀ 0 t0
  have hl02 := hs02 p₀ hp₀ 0 t0
  have hl03 := hs03 p₀ hp₀ 0 t0
  have hl12 := hs12 p₀ hp₀ 0 t0
  have hl13 := hs13 p₀ hp₀ 0 t0
  have hl23 := hs23 p₀ hp₀ 0 t0
  have hrem := te_int_rem (μ := volume) (S := A ×ˢ (B ×ˢ C)) hint dlo dhi first Xm hcXm S1m S2m ?_ ?_ ?_ ?_
  rotate_left
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij <;> simp only [hdlo, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val, Fin.isValue] <;> first
      | exact fx_pos_iff.mpr hd01 | exact fx_pos_iff.mpr hd02 | exact fx_pos_iff.mpr hd03
      | exact fx_pos_iff.mpr hd12 | exact fx_pos_iff.mpr hd13 | exact fx_pos_iff.mpr hd23
      | exact absurd hij (by decide)
  · intro i j hij h2 _
    fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij
    all_goals first | exact absurd hij (by decide) | skip
    all_goals simp only [hdlo, hdhi, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue] at h2 ⊢
    · exact te_mu_nonneg (hl01.1.trans hl01.2) h2
    · exact te_mu_nonneg (hl02.1.trans hl02.2) h2
    · exact te_mu_nonneg (hl03.1.trans hl03.2) h2
    · exact te_mu_nonneg (hl12.1.trans hl12.2) h2
    · exact te_mu_nonneg (hl13.1.trans hl13.2) h2
    · exact te_mu_nonneg (hl23.1.trans hl23.2) h2
  · intro i j hij _
    fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij
    all_goals first | exact absurd hij (by decide) | skip
    all_goals simp only [hXm, hS1m, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    · exact M01.1
    · exact M02.1
    · exact M03.1
    · exact M12.1
    · exact M13.1
    · exact M23.1
  · intro i j hij _
    fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Fin.reduceLT] at hij
    all_goals first | exact absurd hij (by decide) | skip
    all_goals simp only [hXm, hS2m, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    · exact M01.2
    · exact M02.2
    · exact M03.2
    · exact M12.2
    · exact M13.2
    · exact M23.2
  rw [hSV] at hrem
  -- step 5: the code's remainders
  have p01 := te_pair_term hAS hr01 (S1r := S01) (S2r := S01 ^ 2) (by positivity) (sq_nonneg S01) (by rw [te_momentsX3]; exact te_S1_le3 hsqa hsqb hsqc)
    (by rw [te_momentsX3]; exact te_S2_le (by positivity) (te_S1_le3 hsqa hsqb hsqc))
  have p02 := te_pair_term hAS hr02 (S1r := S02) (S2r := S02 ^ 2) (by positivity) (sq_nonneg S02) (by rw [te_momentsX3]; exact te_S1_le3 hsqa hsqb hsqc)
    (by rw [te_momentsX3]; exact te_S2_le (by positivity) (te_S1_le3 hsqa hsqb hsqc))
  have p03 := te_pair_term hAS hr03 (S1r := S03) (S2r := S03 ^ 2) (by positivity) (sq_nonneg S03) (by rw [te_momentsX3]; exact te_S1_le3 hsqa hsqb hsqc)
    (by rw [te_momentsX3]; exact te_S2_le (by positivity) (te_S1_le3 hsqa hsqb hsqc))
  have p12 := te_pair_term hAS hr12 (S1r := S12) (S2r := S12 ^ 2) (by positivity) (sq_nonneg S12) (by rw [te_momentsX3]; exact te_S1_le3 hsqa hsqb hsqc)
    (by rw [te_momentsX3]; exact te_S2_le (by positivity) (te_S1_le3 hsqa hsqb hsqc))
  have p13 := te_pair_term hAS hr13 (S1r := S13) (S2r := S13 ^ 2) (by positivity) (sq_nonneg S13) (by rw [te_momentsX3]; exact te_S1_le3 hsqa hsqb hsqc)
    (by rw [te_momentsX3]; exact te_S2_le (by positivity) (te_S1_le3 hsqa hsqb hsqc))
  have p23 := te_pair_term hAS hr23 (S1r := S23) (S2r := S23 ^ 2) (by positivity) (sq_nonneg S23) (by rw [te_momentsX3]; exact te_S1_le3 hsqa hsqb hsqc)
    (by rw [te_momentsX3]; exact te_S2_le (by positivity) (te_S1_le3 hsqa hsqb hsqc))
  have hsum : (∑ i, ∑ j, if i < j ∧ dlo i j < 2 then
      2 * pairRem (dlo i j) (dhi i j) (first i j) (S1m i j) (S2m i j) else 0) ≤
      fx r01 + fx r02 + fx r03 + fx r12 + fx r13 + fx r23 := by
    simp only [Fin.sum_univ_four, hdlo, hdhi, hfirst, hS1m, hS2m, Fin.isValue, Matrix.cons_val]
    simp (config := { decide := true }) only [Fin.reduceLT, lt_self_iff_false, false_and, true_and, if_false,
      add_zero, zero_add]
    linarith
  -- step 6: combine
  have hVV : 0 ≤ (volume A).toReal * (volume B).toReal * (volume C).toReal := by positivity
  have hgu := (abs_le.mp hgrad).2
  have hfin := mul_le_mul_of_nonneg_right hsum hVV
  have hUV : unionArea c * ((volume A).toReal * (volume B).toReal * (volume C).toReal) ≤
      U * ((volume A).toReal * (volume B).toReal * (volume C).toReal) := mul_le_mul_of_nonneg_right hU hVV
  nlinarith

end BHH.W3
