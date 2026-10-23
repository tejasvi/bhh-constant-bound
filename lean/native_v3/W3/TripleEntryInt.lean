/-
Window-3 entries: the generic integrated vertex lemma.

* Cauchy–Schwarz for set integrals and the moments of a nonnegative linear combination `X = Σ w_s u_s + e`
  (`E X ≤ S1`, `E X² ≤ S1²`, Minkowski; no independence needed);
* integrals over products of two and three planar sets (functions of single coordinates, of the first two, affine
  functions; the centroid `cen` of W2);
* `te_vl_pt`: the vertex lemma along segments (`VertexLemmaSeg`, two-sided) at one configuration of `k` points with
  `ε_i = |y_i - c_i|`, `ν ≤ 2`, and any upper bounds `X_ij ≥ |δ_i| + |δ_j|`;
* `te_int_grad`, `te_int_rem`: the integrated gradient term (`|∇| ≤ 2`) and the integrated remainder (`pairRem` from
  `E X ≤ S1`, `E X² ≤ S2`, W2's `integral_Qf_le`).
-/
import W3.TripleEntryArith
import W2.TabPairAux

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W3

open BHH BHH.W2 BHH.Cert

/-! ## Cauchy–Schwarz and the moments of a nonnegative linear combination -/

section CS

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S : Set Ω}

/-- Cauchy–Schwarz for set integrals (real functions). -/
lemma te_cs {f g : Ω → ℝ} (hf : IntegrableOn (fun ω => f ω ^ 2) S μ) (hg : IntegrableOn (fun ω => g ω ^ 2) S μ)
    (hfg : IntegrableOn (fun ω => f ω * g ω) S μ) :
    ∫ ω in S, f ω * g ω ∂μ ≤ √(∫ ω in S, f ω ^ 2 ∂μ) * √(∫ ω in S, g ω ^ 2 ∂μ) := by
  set A := ∫ ω in S, f ω ^ 2 ∂μ with hA
  set B := ∫ ω in S, g ω ^ 2 ∂μ with hB
  set C := ∫ ω in S, f ω * g ω ∂μ with hC
  have hA0 : 0 ≤ A := setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  have hB0 : 0 ≤ B := setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  -- `0 ≤ ∫ (f - t g)² = A - 2 t C + t² B`
  have key : ∀ t : ℝ, 0 ≤ A - 2 * t * C + t ^ 2 * B := by
    intro t
    have h0 : 0 ≤ ∫ ω in S, (f ω - t * g ω) ^ 2 ∂μ :=
      setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    have e : ∀ ω, (f ω - t * g ω) ^ 2 = f ω ^ 2 - 2 * t * (f ω * g ω) + t ^ 2 * g ω ^ 2 := by
      intro ω; ring
    simp_rw [e] at h0
    have i1 : IntegrableOn (fun ω => f ω ^ 2 - 2 * t * (f ω * g ω)) S μ := hf.sub (hfg.const_mul (2 * t))
    have i2 : IntegrableOn (fun ω => t ^ 2 * g ω ^ 2) S μ := hg.const_mul (t ^ 2)
    have i3 : IntegrableOn (fun ω => 2 * t * (f ω * g ω)) S μ := hfg.const_mul (2 * t)
    rw [integral_add i1 i2, integral_sub hf i3, integral_const_mul, integral_const_mul] at h0
    linarith
  rcases eq_or_lt_of_le hB0 with hB' | hB'
  · -- `B = 0`: then `C ≤ 0`
    have hC0 : C ≤ 0 := by
      by_contra hc
      push_neg at hc
      have := key ((A + 1) / (2 * C))
      rw [← hB'] at this
      field_simp at this
      nlinarith
    exact hC0.trans (by positivity)
  · have h1 := key (C / B)
    have h2 : C ^ 2 ≤ A * B := by
      have : A - 2 * (C / B) * C + (C / B) ^ 2 * B = A - C ^ 2 / B := by field_simp; ring
      rw [this] at h1
      exact (div_le_iff₀ hB').mp (by linarith)
    rw [← Real.sqrt_mul hA0]
    exact Real.le_sqrt_of_sq_le h2

end CS

section Mom

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] {μ : Measure Ω} {S : Set Ω}

/-- first moment from the second (Cauchy–Schwarz with `1`) -/
lemma te_mom1 (hint : ∀ f : Ω → ℝ, Continuous f → IntegrableOn f S μ) (hSt : μ S ≠ ⊤) {f : Ω → ℝ}
    (cf : Continuous f) {F : ℝ} (hF : 0 ≤ F) (h2 : ∫ ω in S, f ω ^ 2 ∂μ ≤ F ^ 2 * (μ S).toReal) :
    ∫ ω in S, f ω ∂μ ≤ F * (μ S).toReal := by
  have h := te_cs (μ := μ) (S := S) (f := f) (g := fun _ => (1 : ℝ)) (hint (fun ω => f ω ^ 2) (cf.pow 2))
    (hint (fun _ => (1 : ℝ) ^ 2) continuous_const) (hint (fun ω => f ω * 1) (cf.mul continuous_const))
  simp only [mul_one, one_pow] at h
  rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def] at h
  have hV : 0 ≤ (μ S).toReal := ENNReal.toReal_nonneg
  calc ∫ ω in S, f ω ∂μ ≤ √(∫ ω in S, f ω ^ 2 ∂μ) * √((μ S).toReal) := h
    _ ≤ √(F ^ 2 * (μ S).toReal) * √((μ S).toReal) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
    _ = F * (μ S).toReal := by
        rw [Real.sqrt_mul (sq_nonneg F), Real.sqrt_sq hF, mul_assoc, Real.mul_self_sqrt hV]

/-- Minkowski for two functions in `L²(S)` (second moments relative to `|S|`) -/
lemma te_mink (hint : ∀ f : Ω → ℝ, Continuous f → IntegrableOn f S μ) {f g : Ω → ℝ}
    (cf : Continuous f) (cg : Continuous g) {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hf : ∫ ω in S, f ω ^ 2 ∂μ ≤ F ^ 2 * (μ S).toReal) (hg : ∫ ω in S, g ω ^ 2 ∂μ ≤ G ^ 2 * (μ S).toReal) :
    ∫ ω in S, (f ω + g ω) ^ 2 ∂μ ≤ (F + G) ^ 2 * (μ S).toReal := by
  have hV : 0 ≤ (μ S).toReal := ENNReal.toReal_nonneg
  have hcs := te_cs (μ := μ) (S := S) (hint (fun ω => f ω ^ 2) (cf.pow 2)) (hint (fun ω => g ω ^ 2) (cg.pow 2))
    (hint (fun ω => f ω * g ω) (cf.mul cg))
  have e : ∀ ω, (f ω + g ω) ^ 2 = f ω ^ 2 + 2 * (f ω * g ω) + g ω ^ 2 := fun ω => by ring
  simp_rw [e]
  have i1 : IntegrableOn (fun ω => f ω ^ 2 + 2 * (f ω * g ω)) S μ :=
    hint _ ((cf.pow 2).add (continuous_const.mul (cf.mul cg)))
  rw [integral_add i1 (hint (fun ω => g ω ^ 2) (cg.pow 2)), integral_add (hint (fun ω => f ω ^ 2) (cf.pow 2))
    (hint (fun ω => 2 * (f ω * g ω)) (continuous_const.mul (cf.mul cg))), integral_const_mul]
  have hfg : √(∫ ω in S, f ω ^ 2 ∂μ) * √(∫ ω in S, g ω ^ 2 ∂μ) ≤ F * G * (μ S).toReal := by
    calc √(∫ ω in S, f ω ^ 2 ∂μ) * √(∫ ω in S, g ω ^ 2 ∂μ)
        ≤ √(F ^ 2 * (μ S).toReal) * √(G ^ 2 * (μ S).toReal) :=
          mul_le_mul (Real.sqrt_le_sqrt hf) (Real.sqrt_le_sqrt hg) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = F * G * (μ S).toReal := by
          rw [Real.sqrt_mul (sq_nonneg F), Real.sqrt_mul (sq_nonneg G), Real.sqrt_sq hF, Real.sqrt_sq hG]
          have := Real.mul_self_sqrt hV
          calc F * √(μ S).toReal * (G * √(μ S).toReal) = F * G * (√(μ S).toReal * √(μ S).toReal) := by ring
            _ = _ := by rw [this]
  nlinarith

omit [TopologicalSpace Ω] in
/-- second moment of `w · u` from that of `u` -/
lemma te_mom_smul {u : Ω → ℝ} {m w : ℝ} (hm0 : 0 ≤ m)
    (h : ∫ ω in S, u ω ^ 2 ∂μ ≤ m * (μ S).toReal) :
    ∫ ω in S, (w * u ω) ^ 2 ∂μ ≤ (w * √m) ^ 2 * (μ S).toReal := by
  have e : ∀ ω, (w * u ω) ^ 2 = w ^ 2 * u ω ^ 2 := fun ω => by ring
  simp_rw [e]
  rw [integral_const_mul, mul_pow, Real.sq_sqrt hm0, mul_assoc]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg w)

omit [TopologicalSpace Ω] in
lemma te_mom_const {e : ℝ} :
    ∫ ω in S, (fun _ => e) ω ^ 2 ∂μ ≤ e ^ 2 * (μ S).toReal := by
  rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]

/-- The moments of `X = wa ua + wb ub + wc uc + e`: `E X ≤ S1`, `E X² ≤ S1²` with `S1 = Σ w √m + e`
(Minkowski). -/
lemma te_moments3 (hint : ∀ f : Ω → ℝ, Continuous f → IntegrableOn f S μ) (hSt : μ S ≠ ⊤)
    {ua ub uc : Ω → ℝ} (ca : Continuous ua) (cb : Continuous ub) (cc : Continuous uc)
    {ma mb mc wa wb wc e : ℝ} (hma0 : 0 ≤ ma) (hmb0 : 0 ≤ mb) (hmc0 : 0 ≤ mc)
    (hwa : 0 ≤ wa) (hwb : 0 ≤ wb) (hwc : 0 ≤ wc) (he : 0 ≤ e)
    (hma : ∫ ω in S, ua ω ^ 2 ∂μ ≤ ma * (μ S).toReal) (hmb : ∫ ω in S, ub ω ^ 2 ∂μ ≤ mb * (μ S).toReal)
    (hmc : ∫ ω in S, uc ω ^ 2 ∂μ ≤ mc * (μ S).toReal) :
    ∫ ω in S, (wa * ua ω + wb * ub ω + wc * uc ω + e) ∂μ ≤
        (wa * √ma + wb * √mb + wc * √mc + e) * (μ S).toReal ∧
      ∫ ω in S, (wa * ua ω + wb * ub ω + wc * uc ω + e) ^ 2 ∂μ ≤
        (wa * √ma + wb * √mb + wc * √mc + e) ^ 2 * (μ S).toReal := by
  have h1 := te_mink hint ((continuous_const.mul ca)) (continuous_const.mul cb)
    (mul_nonneg hwa (Real.sqrt_nonneg _)) (mul_nonneg hwb (Real.sqrt_nonneg _))
    (te_mom_smul hma0 hma) (te_mom_smul hmb0 hmb)
  have h2 := te_mink hint ((continuous_const.mul ca).add (continuous_const.mul cb)) (continuous_const.mul cc)
    (add_nonneg (mul_nonneg hwa (Real.sqrt_nonneg _)) (mul_nonneg hwb (Real.sqrt_nonneg _)))
    (mul_nonneg hwc (Real.sqrt_nonneg _)) h1 (te_mom_smul hmc0 hmc)
  have h3 := te_mink hint (((continuous_const.mul ca).add (continuous_const.mul cb)).add
    (continuous_const.mul cc)) continuous_const
    (add_nonneg (add_nonneg (mul_nonneg hwa (Real.sqrt_nonneg _)) (mul_nonneg hwb (Real.sqrt_nonneg _)))
      (mul_nonneg hwc (Real.sqrt_nonneg _))) he h2 (te_mom_const (e := e))
  have hS : 0 ≤ wa * √ma + wb * √mb + wc * √mc + e := by positivity
  refine ⟨te_mom1 hint hSt ((((continuous_const.mul ca).add (continuous_const.mul cb)).add
    (continuous_const.mul cc)).add continuous_const) hS h3, h3⟩

end Mom

/-! ## Integrals over products of two and three planar sets -/

section prod3

variable {A B C : Set Pt}

lemma te_vol2 (A B : Set Pt) : (volume (A ×ˢ B)).toReal = (volume A).toReal * (volume B).toReal := by
  rw [Measure.volume_eq_prod (α := Pt) (β := Pt), Measure.prod_prod, ENNReal.toReal_mul]

lemma te_vol3 (A B C : Set Pt) :
    (volume (A ×ˢ (B ×ˢ C))).toReal = (volume A).toReal * (volume B).toReal * (volume C).toReal := by
  rw [Measure.volume_eq_prod (α := Pt) (β := Pt × Pt), Measure.prod_prod, ENNReal.toReal_mul, te_vol2, mul_assoc]

lemma te_int2_fst (f : Pt → ℝ) : ∫ p in A ×ˢ B, f p.1 = (∫ x in A, f x) * (volume B).toReal := by
  have h := setIntegral_prod_mul (μ := (volume : Measure Pt)) (ν := (volume : Measure Pt)) f (fun _ => (1 : ℝ)) A B
  simp only [mul_one] at h
  rw [Measure.volume_eq_prod (α := Pt) (β := Pt), h, setIntegral_const, measureReal_def, smul_eq_mul, mul_one]

lemma te_int2_snd (f : Pt → ℝ) : ∫ p in A ×ˢ B, f p.2 = (volume A).toReal * ∫ x in B, f x := by
  have h := setIntegral_prod_mul (μ := (volume : Measure Pt)) (ν := (volume : Measure Pt)) (fun _ => (1 : ℝ)) f A B
  simp only [one_mul] at h
  rw [Measure.volume_eq_prod (α := Pt) (β := Pt), h, setIntegral_const, measureReal_def, smul_eq_mul, mul_one]

lemma te_int3_fst (f : Pt → ℝ) :
    ∫ p in A ×ˢ (B ×ˢ C), f p.1 = (∫ x in A, f x) * ((volume B).toReal * (volume C).toReal) := by
  have h := setIntegral_prod_mul (μ := (volume : Measure Pt)) (ν := (volume : Measure (Pt × Pt))) f
    (fun _ => (1 : ℝ)) A (B ×ˢ C)
  simp only [mul_one] at h
  rw [Measure.volume_eq_prod (α := Pt) (β := Pt × Pt), h, setIntegral_const, measureReal_def, smul_eq_mul,
    mul_one, te_vol2]

lemma te_int3_snd (f : Pt × Pt → ℝ) :
    ∫ p in A ×ˢ (B ×ˢ C), f p.2 = (volume A).toReal * ∫ q in B ×ˢ C, f q := by
  have h := setIntegral_prod_mul (μ := (volume : Measure Pt)) (ν := (volume : Measure (Pt × Pt)))
    (fun _ => (1 : ℝ)) f A (B ×ˢ C)
  simp only [one_mul] at h
  rw [Measure.volume_eq_prod (α := Pt) (β := Pt × Pt), h, setIntegral_const, measureReal_def, smul_eq_mul, mul_one]

lemma te_int3_mid (f : Pt → ℝ) :
    ∫ p in A ×ˢ (B ×ˢ C), f p.2.1 = (volume A).toReal * ((∫ x in B, f x) * (volume C).toReal) := by
  rw [te_int3_snd (fun q => f q.1), te_int2_fst]

lemma te_int3_lst (f : Pt → ℝ) :
    ∫ p in A ×ˢ (B ×ˢ C), f p.2.2 = (volume A).toReal * ((volume B).toReal * ∫ x in C, f x) := by
  rw [te_int3_snd (fun q => f q.2), te_int2_snd]

/-- a function of the first two coordinates -/
lemma te_int3_fst12 (f : Pt × Pt → ℝ) :
    ∫ p in A ×ˢ (B ×ˢ C), f (p.1, p.2.1) = (∫ q in A ×ˢ B, f q) * (volume C).toReal := by
  have hmp := measurePreserving_prodAssoc (volume : Measure Pt) (volume : Measure Pt) (volume : Measure Pt)
  have h := hmp.setIntegral_preimage_emb (MeasurableEquiv.prodAssoc).measurableEmbedding
    (fun p : Pt × (Pt × Pt) => f (p.1, p.2.1)) (A ×ˢ (B ×ˢ C))
  have hpre : (MeasurableEquiv.prodAssoc : (Pt × Pt) × Pt ≃ᵐ Pt × (Pt × Pt)) ⁻¹' (A ×ˢ (B ×ˢ C)) =
      (A ×ˢ B) ×ˢ C := by
    ext ⟨⟨x, y⟩, z⟩; simp [MeasurableEquiv.prodAssoc, and_assoc]
  rw [hpre] at h
  have h2 := setIntegral_prod_mul (μ := (volume : Measure (Pt × Pt))) (ν := (volume : Measure Pt)) f
    (fun _ => (1 : ℝ)) (A ×ˢ B) C
  simp only [mul_one] at h2
  rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one] at h2
  have e : (volume : Measure (Pt × (Pt × Pt))) = (volume : Measure Pt).prod ((volume : Measure Pt).prod volume) := by
    rw [Measure.volume_eq_prod (α := Pt) (β := Pt × Pt), Measure.volume_eq_prod (α := Pt) (β := Pt)]
  calc ∫ p in A ×ˢ (B ×ˢ C), f (p.1, p.2.1)
      = ∫ y in A ×ˢ (B ×ˢ C), f (y.1, y.2.1) ∂((volume : Measure Pt).prod ((volume : Measure Pt).prod volume)) := by
        rw [e]
    _ = ∫ x in (A ×ˢ B) ×ˢ C, f ((MeasurableEquiv.prodAssoc x).1, (MeasurableEquiv.prodAssoc x).2.1)
          ∂(((volume : Measure Pt).prod (volume : Measure Pt)).prod volume) := h.symm
    _ = ∫ x in (A ×ˢ B) ×ˢ C, f x.1 ∂(((volume : Measure Pt).prod (volume : Measure Pt)).prod volume) := rfl
    _ = ∫ x in (A ×ˢ B) ×ˢ C, f x.1 ∂((volume : Measure (Pt × Pt)).prod volume) := by
        rw [← Measure.volume_eq_prod (α := Pt) (β := Pt)]
    _ = _ := h2

end prod3

/-! ## The vertex lemma along segments, pointwise, for `k` points -/

/-- the gradient term `⟨∇_{y_i} A(c), δ⟩` -/
def teGrad {k : ℕ} (c : Fin k → Pt) (i : Fin k) (δ : Pt) : ℝ :=
  (greenGrad c i).1 * δ.1 + (greenGrad c i).2 * δ.2

/-- the pointwise bound of the vertex remainder: `Σ_{i<j, d⁻_ij<2} 2 Qf_ij(X_ij)` (`ν ≤ 2`) -/
def teRem {k : ℕ} (dlo dhi : Fin k → Fin k → ℝ) (first : Fin k → Fin k → Bool) (X : Fin k → Fin k → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j ∧ dlo i j < 2 then 2 * Qf (dlo i j) (dhi i j) (first i j) (X i j) else 0

lemma te_nu_le_two {k : ℕ} (c : Fin k → Pt) (eps : Fin k → ℝ) (dlo dhi : Fin k → Fin k → ℝ)
    (first : Fin k → Fin k → Bool) (i j : Fin k) : (nuCountSeg c eps dlo dhi first i j : ℝ) ≤ 2 := by
  have : nuCountSeg c eps dlo dhi first i j ≤ 2 := by
    unfold nuCountSeg; simp only; split_ifs <;> omega
  exact_mod_cast this

lemma te_mu_nonneg {dlo dhi : ℝ} (hle : dlo ≤ dhi) (h2 : dlo < 2) :
    0 ≤ 2 * Real.arcsin (min dhi 2 / 2) - 2 * Real.arcsin (dlo / 2) := by
  have hle' : dlo ≤ min dhi 2 := le_min hle h2.le
  have := Real.arcsin_le_arcsin (div_le_div_of_nonneg_right hle' (by norm_num : (0 : ℝ) ≤ 2))
  linarith

lemma te_Tseg_nonneg {dlo dhi : ℝ} {first : Bool} {D : ℝ} (hdlo : 0 < dlo) (hD : 0 ≤ D)
    (hμ : first = false → 0 ≤ 2 * Real.arcsin (min dhi 2 / 2) - 2 * Real.arcsin (dlo / 2)) :
    0 ≤ Tseg dlo dhi first D := by
  unfold Tseg
  have h2 : 0 ≤ min (D / dlo) π := le_min (div_nonneg hD hdlo.le) Real.pi_pos.le
  cases first with
  | true =>
    simp only [if_true]
    have := div_nonneg hD (Real.sqrt_nonneg (4 - dhi ^ 2)); linarith
  | false => simp only [Bool.false_eq_true, if_false]; linarith [hμ rfl]

/-- The vertex lemma along segments at one configuration, with `ε_i = |y_i - c_i|` and the remainder bounded by
`Σ 2 Qf(X_ij)` for any `X_ij ≥ |δ_i| + |δ_j|` (two-sided). -/
theorem te_vl_pt (hV : VertexLemmaSeg) {k : ℕ} {c y : Fin k → Pt} {dlo dhi : Fin k → Fin k → ℝ}
    {first : Fin k → Fin k → Bool} {X : Fin k → Fin k → ℝ}
    (hdlo : ∀ i j, i < j → 0 < dlo i j)
    (hseg : ∀ i j, i < j → ∀ t ∈ Icc (0 : ℝ) 1,
        dlo i j ≤ edist2 (segPt (c i) (y i) t) (segPt (c j) (y j) t) ∧
        edist2 (segPt (c i) (y i) t) (segPt (c j) (y j) t) ≤ dhi i j)
    (hfirst : ∀ i j, i < j → first i j = true → dhi i j < 2)
    (hX : ∀ i j, i < j → enorm2 (y i - c i) + enorm2 (y j - c j) ≤ X i j) :
    |unionArea y - unionArea c - ∑ i, teGrad c i (y i - c i)| ≤ teRem dlo dhi first X := by
  have h := hV k c y (fun i => enorm2 (y i - c i)) dlo dhi first hdlo hseg hfirst (fun i => le_rfl)
  refine h.trans ?_
  unfold vertexRemSeg teRem
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  by_cases hij : i < j ∧ dlo i j < 2
  · rw [if_pos hij, if_pos hij]
    have h0 := hseg i j hij.1 0 ⟨le_rfl, zero_le_one⟩
    have hle : dlo i j ≤ dhi i j := h0.1.trans h0.2
    have hμ : first i j = false →
        0 ≤ 2 * Real.arcsin (min (dhi i j) 2 / 2) - 2 * Real.arcsin (dlo i j / 2) :=
      fun _ => te_mu_nonneg hle hij.2
    have ha : 0 ≤ enorm2 (y i - c i) := Real.sqrt_nonneg _
    have hb : 0 ≤ enorm2 (y j - c j) := Real.sqrt_nonneg _
    have hD0 : 0 ≤ enorm2 ((y j - c j) - (y i - c i)) := Real.sqrt_nonneg _
    have hDab : enorm2 ((y j - c j) - (y i - c i)) ≤ enorm2 (y i - c i) + enorm2 (y j - c j) := by
      have := tp_enorm2_sub_le (y j - c j) (y i - c i); linarith
    have hT := te_Tseg_nonneg (first := first i j) (dhi := dhi i j) (hdlo i j hij.1) hD0 hμ
    have hXij := hX i j hij.1
    have hQ := mul_Tseg_le_Qf (hdlo i j hij.1) (hfirst i j hij.1) (le_trans (add_nonneg ha hb) hXij) hD0
      (hDab.trans hXij)
    have hν := te_nu_le_two c (fun i => enorm2 (y i - c i)) dlo dhi first i j
    have hν0 : (0 : ℝ) ≤ (nuCountSeg c (fun i => enorm2 (y i - c i)) dlo dhi first i j : ℝ) := Nat.cast_nonneg _
    have hP : 0 ≤ (enorm2 (y i - c i) + enorm2 (y j - c j)) * Tseg (dlo i j) (dhi i j) (first i j)
        (enorm2 ((y j - c j) - (y i - c i))) := mul_nonneg (add_nonneg ha hb) hT
    calc (nuCountSeg c (fun i => enorm2 (y i - c i)) dlo dhi first i j : ℝ) *
          (enorm2 (y i - c i) + enorm2 (y j - c j)) *
          Tseg (dlo i j) (dhi i j) (first i j) (enorm2 ((y j - c j) - (y i - c i)))
        ≤ 2 * ((enorm2 (y i - c i) + enorm2 (y j - c j)) *
          Tseg (dlo i j) (dhi i j) (first i j) (enorm2 ((y j - c j) - (y i - c i)))) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hν hP
      _ ≤ 2 * (X i j * Tseg (dlo i j) (dhi i j) (first i j) (enorm2 ((y j - c j) - (y i - c i)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXij hT) (by norm_num)
      _ ≤ 2 * Qf (dlo i j) (dhi i j) (first i j) (X i j) := mul_le_mul_of_nonneg_left hQ (by norm_num)
  · rw [if_neg hij, if_neg hij]

/-! ## The integrated pieces -/

section Int

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] {μ : Measure Ω} {S : Set Ω}

lemma te_abs_grad_le {k : ℕ} (c : Fin k → Pt) (i : Fin k) (δ : Pt) : |teGrad c i δ| ≤ 2 * enorm2 δ := by
  have hg : enorm2 (greenGrad c i) ≤ 2 := by
    have h4 := greenGradLe k c i
    unfold enorm2
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt h4
  have h1 : teGrad c i δ ≤ enorm2 (greenGrad c i) * enorm2 δ := tp_inner_le_enorm2 _ _
  have h2 : -teGrad c i δ ≤ enorm2 (greenGrad c i) * enorm2 (-δ) := by
    have := tp_inner_le_enorm2 (greenGrad c i) (-δ)
    unfold teGrad; simp only [Prod.fst_neg, Prod.snd_neg] at this ⊢; linarith
  have hn : enorm2 (-δ) = enorm2 δ := by unfold enorm2; simp
  rw [hn] at h2
  have hδ : 0 ≤ enorm2 δ := Real.sqrt_nonneg _
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hg hδ]

/-- The gradient term integrates to `|S| Σ_i ⟨∇_i A(c), D_i⟩` (`D_i` the mean displacement), of absolute value at most
`2 |S| Σ_i e_i` when `|D_i| ≤ e_i`. -/
lemma te_int_grad (hint : ∀ f : Ω → ℝ, Continuous f → IntegrableOn f S μ) {k : ℕ} (c : Fin k → Pt)
    (Y : Ω → Fin k → Pt) (hY : ∀ i, Continuous fun ω => Y ω i) (Dm : Fin k → Pt)
    (hD : ∀ i, ∫ ω in S, (Y ω i - c i).1 ∂μ = (μ S).toReal * (Dm i).1 ∧
      ∫ ω in S, (Y ω i - c i).2 ∂μ = (μ S).toReal * (Dm i).2)
    (e : Fin k → ℝ) (he : ∀ i, enorm2 (Dm i) ≤ e i) :
    |∫ ω in S, ∑ i, teGrad c i (Y ω i - c i) ∂μ| ≤ 2 * (∑ i, e i) * (μ S).toReal := by
  have hV : 0 ≤ (μ S).toReal := ENNReal.toReal_nonneg
  have hc1 : ∀ i, Continuous fun ω => (Y ω i - c i).1 := fun i => ((hY i).sub continuous_const).fst
  have hc2 : ∀ i, Continuous fun ω => (Y ω i - c i).2 := fun i => ((hY i).sub continuous_const).snd
  have hterm : ∀ i, ∫ ω in S, teGrad c i (Y ω i - c i) ∂μ = (μ S).toReal * teGrad c i (Dm i) := by
    intro i
    unfold teGrad
    rw [integral_add ((hint _ (hc1 i)).const_mul _) ((hint _ (hc2 i)).const_mul _), integral_const_mul,
      integral_const_mul, (hD i).1, (hD i).2]
    ring
  have hcG : ∀ i, Continuous fun ω => teGrad c i (Y ω i - c i) := by
    intro i; unfold teGrad; have h1 := hc1 i; have h2 := hc2 i; fun_prop
  rw [integral_finset_sum _ (fun i _ => hint _ (hcG i))]
  simp_rw [hterm]
  rw [← Finset.mul_sum, abs_mul, abs_of_nonneg hV]
  have hs : |∑ i, teGrad c i (Dm i)| ≤ 2 * ∑ i, e i := by
    calc |∑ i, teGrad c i (Dm i)| ≤ ∑ i, |teGrad c i (Dm i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, 2 * e i := Finset.sum_le_sum fun i _ => (te_abs_grad_le c i (Dm i)).trans (by linarith [he i])
      _ = 2 * ∑ i, e i := by rw [Finset.mul_sum]
  calc (μ S).toReal * |∑ i, teGrad c i (Dm i)| ≤ (μ S).toReal * (2 * ∑ i, e i) := mul_le_mul_of_nonneg_left hs hV
    _ = 2 * (∑ i, e i) * (μ S).toReal := by ring

/-- The remainder bound integrates to at most `|S| Σ_{i<j, d⁻<2} 2 pairRem(S1_ij, S2_ij)`. -/
lemma te_int_rem (hint : ∀ f : Ω → ℝ, Continuous f → IntegrableOn f S μ) {k : ℕ} (dlo dhi : Fin k → Fin k → ℝ)
    (first : Fin k → Fin k → Bool) (Xb : Fin k → Fin k → Ω → ℝ) (hXc : ∀ i j, Continuous (Xb i j))
    (S1 S2 : Fin k → Fin k → ℝ) (hdlo : ∀ i j, i < j → 0 < dlo i j)
    (hμ : ∀ i j, i < j → dlo i j < 2 → first i j = false →
      0 ≤ 2 * Real.arcsin (min (dhi i j) 2 / 2) - 2 * Real.arcsin (dlo i j / 2))
    (h1 : ∀ i j, i < j → dlo i j < 2 → ∫ ω in S, Xb i j ω ∂μ ≤ S1 i j * (μ S).toReal)
    (h2 : ∀ i j, i < j → dlo i j < 2 → ∫ ω in S, Xb i j ω ^ 2 ∂μ ≤ S2 i j * (μ S).toReal) :
    ∫ ω in S, teRem dlo dhi first (fun i j => Xb i j ω) ∂μ ≤
      (∑ i, ∑ j, if i < j ∧ dlo i j < 2 then
        2 * pairRem (dlo i j) (dhi i j) (first i j) (S1 i j) (S2 i j) else 0) * (μ S).toReal := by
  have hV : 0 ≤ (μ S).toReal := ENNReal.toReal_nonneg
  have hcQ : ∀ i j, Continuous fun ω => Qf (dlo i j) (dhi i j) (first i j) (Xb i j ω) :=
    fun i j => (continuous_Qf _ _ _).comp (hXc i j)
  have hcT : ∀ i j, Continuous fun ω =>
      (if i < j ∧ dlo i j < 2 then 2 * Qf (dlo i j) (dhi i j) (first i j) (Xb i j ω) else 0) := by
    intro i j; split_ifs
    · exact continuous_const.mul (hcQ i j)
    · exact continuous_const
  unfold teRem
  rw [integral_finset_sum _ (fun i _ => hint _ (continuous_finset_sum _ fun j _ => hcT i j))]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum; intro i _
  rw [integral_finset_sum _ (fun j _ => hint _ (hcT i j)), Finset.sum_mul]
  apply Finset.sum_le_sum; intro j _
  by_cases hij : i < j ∧ dlo i j < 2
  · simp only [hij, and_self, if_true]
    rw [integral_const_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact integral_Qf_le (hint _ (hXc i j)) (hint _ ((hXc i j).pow 2)) hV (h1 i j hij.1 hij.2)
      (h2 i j hij.1 hij.2) (hdlo i j hij.1) (hμ i j hij.1 hij.2)
  · simp only [hij, if_false, integral_zero, zero_mul, le_refl]

end Int


/-! ## Configuration helpers -/

lemma te_edist2_seg (ci yi cj yj m z : Pt) (t : ℝ) (hm : cj - ci = m) (hz : yj - yi = z) :
    edist2 (segPt ci yi t) (segPt cj yj t) = enorm2 (m + t • (z - m)) := by
  have e : segPt cj yj t - segPt ci yi t = m + t • (z - m) := by
    rw [← hm, ← hz]; unfold segPt; ext <;> simp <;> ring
  rw [← e]
  unfold edist2 enorm2 sqDist
  congr 1
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

lemma te_enorm2_neg (u : Pt) : enorm2 (-u) = enorm2 u := by unfold enorm2; simp

lemma te_enorm2_add_le (u v : Pt) : enorm2 (u + v) ≤ enorm2 u + enorm2 v := by
  have := tp_enorm2_sub_le u (-v)
  rwa [sub_neg_eq_add, te_enorm2_neg] at this

lemma te_enorm2_sub_eq (u v : Pt) : enorm2 (u - v) = edist2 u v := rfl

lemma te_enorm2_sq' (u v : Pt) : enorm2 (u - v) ^ 2 = sqDist u v := by
  rw [te_enorm2_sub_eq]; unfold edist2; exact Real.sq_sqrt (by unfold sqDist; positivity)

lemma te_cen_mul {W : Set Pt} (hW0 : volume W ≠ 0) (hWt : volume W ≠ ⊤) :
    ∫ w in W, w.1 = (volume W).toReal * (cen W).1 ∧ ∫ w in W, w.2 = (volume W).toReal * (cen W).2 := by
  have hV : (volume W).toReal ≠ 0 := (ENNReal.toReal_pos hW0 hWt).ne'
  simp only [cen]
  constructor <;> field_simp


lemma te_d0 (z z' C C' c0 : Pt) :
    enorm2 (-(z + z') - c0) ≤ enorm2 (z - C) + enorm2 (z' - C') + edist2 (C + C') (-c0) := by
  have e : -(z + z') - c0 = -((z - C) + (z' - C') + ((C + C') - -c0)) := by abel
  rw [e, te_enorm2_neg, ← te_enorm2_sub_eq (C + C')]
  calc enorm2 (z - C + (z' - C') + (C + C' - -c0)) ≤ enorm2 (z - C + (z' - C')) + enorm2 (C + C' - -c0) :=
        te_enorm2_add_le _ _
    _ ≤ enorm2 (z - C) + enorm2 (z' - C') + enorm2 (C + C' - -c0) := by
        linarith [te_enorm2_add_le (z - C) (z' - C')]

lemma te_d1 (z' C' c1 : Pt) : enorm2 (-z' - c1) ≤ enorm2 (z' - C') + edist2 C' (-c1) := by
  have e : -z' - c1 = -((z' - C') + (C' - -c1)) := by abel
  rw [e, te_enorm2_neg, ← te_enorm2_sub_eq C']
  exact te_enorm2_add_le _ _

lemma te_d3 (z C c3 : Pt) : enorm2 (z - c3) ≤ enorm2 (z - C) + edist2 C c3 := by
  have e : z - c3 = (z - C) + (C - c3) := by abel
  rw [e, ← te_enorm2_sub_eq C]
  exact te_enorm2_add_le _ _

lemma te_enorm2_zero : enorm2 (0 : Pt) = 0 := by unfold enorm2; simp

/-- the real `S1` of the code's `momentsX` dominates `Σ w √m + e` -/
lemma te_S1_le {wa wb : ℕ} {sqa sqb e : ℤ} {ma mb : ℝ} (ha : √ma ≤ fx sqa) (hb : √mb ≤ fx sqb) :
    (wa : ℝ) * √ma + (wb : ℝ) * √mb + 0 * √0 + fx e ≤ fx (e + wa * sqa + wb * sqb) := by
  rw [te_fx_add, te_fx_add, te_fx_natMul, te_fx_natMul]
  have h1 := mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg wa)
  have h2 := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg wb)
  simp only [Real.sqrt_zero, mul_zero, add_zero]
  linarith

lemma te_S2_le {s : ℤ} {S : ℝ} (h0 : 0 ≤ S) (h : S ≤ fx s) : S ^ 2 ≤ fx (shrU (s * s) PR + 1) := by
  have := te_fx_shrU_mul s s
  nlinarith

/-- `2 · pairRem` of a pair is at most the code's remainder (or the pair is not counted). -/
lemma te_pair_term (hAS : AsinTSound) {dn dx s1 s2 r : ℤ} (hr : W3C.lvPairT W3C.mkAsinTab dn dx s1 s2 = some r)
    {S1r S2r : ℝ} (hS1 : 0 ≤ S1r) (hS2 : 0 ≤ S2r) (hS1r : S1r ≤ fx s1) (hS2r : S2r ≤ fx s2) :
    (if fx dn < 2 then 2 * pairRem (fx dn) (fx dx) (decide (W2C.useFirstOf dx)) S1r S2r else 0) ≤ fx r := by
  obtain ⟨-, hz, hb⟩ := te_lvPairT_spec hAS hr
  split_ifs with h
  · have hlt : dn < 2 * ONE := by
      by_contra hc; push_neg at hc; have := te_fx_mono hc; rw [te_fx_two_ONE] at this; linarith
    exact hb hlt S1r S2r hS1 hS2 hS1r hS2r
  · have hge : 2 * ONE ≤ dn := by
      by_contra hc; push_neg at hc; have := te_fx_lt hc; rw [te_fx_two_ONE] at this; exact h this
    rw [hz hge, te_fx_zero]


/-- integral over `Z × Z'` of a separated function -/
lemma te_int2_sep {Z Z' : Set Pt} (hint : ∀ F : Pt × Pt → ℝ, Continuous F → IntegrableOn F (Z ×ˢ Z'))
    (hSt : volume (Z ×ˢ Z') ≠ ⊤) {f g : Pt → ℝ} (hf : Continuous f) (hg : Continuous g) (k : ℝ) :
    ∫ p in Z ×ˢ Z', (f p.1 + g p.2 + k) =
      (∫ z in Z, f z) * (volume Z').toReal + (volume Z).toReal * (∫ z in Z', g z) +
        k * ((volume Z).toReal * (volume Z').toReal) := by
  have i1 : IntegrableOn (fun p : Pt × Pt => f p.1) (Z ×ˢ Z') := hint _ (hf.comp continuous_fst)
  have i2 : IntegrableOn (fun p : Pt × Pt => g p.2) (Z ×ˢ Z') := hint _ (hg.comp continuous_snd)
  have i12 : IntegrableOn (fun p : Pt × Pt => f p.1 + g p.2) (Z ×ˢ Z') := i1.add i2
  rw [integral_add i12 (integrableOn_const hSt), integral_add i1 i2, te_int2_fst, te_int2_snd,
    setIntegral_const, measureReal_def, te_vol2, smul_eq_mul, mul_comm k]

/-- the mean of the first coordinate over a set, negated -/
lemma te_int_neg_fst {W : Set Pt} (hW0 : volume W ≠ 0) (hWt : volume W ≠ ⊤) :
    ∫ z in W, -z.1 = (volume W).toReal * -(cen W).1 := by
  rw [integral_neg, (te_cen_mul hW0 hWt).1]; ring

lemma te_int_neg_snd {W : Set Pt} (hW0 : volume W ≠ 0) (hWt : volume W ≠ ⊤) :
    ∫ z in W, -z.2 = (volume W).toReal * -(cen W).2 := by
  rw [integral_neg, (te_cen_mul hW0 hWt).2]; ring

lemma te_int_zero {W : Set Pt} : ∫ _z in W, (0 : ℝ) = 0 := integral_zero _ _

/-- integral over `Z × Z'` of an affine function of the four coordinates -/
lemma te_int2_aff {Z Z' : Set Pt} (hZ0 : volume Z ≠ 0) (hZt : volume Z ≠ ⊤) (hZ'0 : volume Z' ≠ 0)
    (hZ't : volume Z' ≠ ⊤) (hint : ∀ F : Pt × Pt → ℝ, Continuous F → IntegrableOn F (Z ×ˢ Z'))
    (hZi : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f Z) (hZ'i : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f Z')
    (a b a' b' k : ℝ) :
    ∫ p in Z ×ˢ Z', (a * p.1.1 + b * p.1.2 + (a' * p.2.1 + b' * p.2.2) + k) =
      (volume Z).toReal * (volume Z').toReal *
        (a * (cen Z).1 + b * (cen Z).2 + (a' * (cen Z').1 + b' * (cen Z').2) + k) := by
  have hSt : volume (Z ×ˢ Z') ≠ ⊤ := by
    rw [Measure.volume_eq_prod (α := Pt) (β := Pt), Measure.prod_prod]; exact ENNReal.mul_ne_top hZt hZ't
  rw [te_int2_sep (f := fun z : Pt => a * z.1 + b * z.2) (g := fun z : Pt => a' * z.1 + b' * z.2) hint hSt
    (by fun_prop) (by fun_prop) k]
  obtain ⟨h1, h2⟩ := te_cen_mul hZ0 hZt
  obtain ⟨h1', h2'⟩ := te_cen_mul hZ'0 hZ't
  have i1 : IntegrableOn (fun z : Pt => a * z.1) Z := hZi _ (by fun_prop)
  have i2 : IntegrableOn (fun z : Pt => b * z.2) Z := hZi _ (by fun_prop)
  have i1' : IntegrableOn (fun z : Pt => a' * z.1) Z' := hZ'i _ (by fun_prop)
  have i2' : IntegrableOn (fun z : Pt => b' * z.2) Z' := hZ'i _ (by fun_prop)
  rw [integral_add i1 i2, integral_add i1' i2', integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, h1, h2, h1', h2']
  ring

end BHH.W3
