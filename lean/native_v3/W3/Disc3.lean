/-
The discretisation bound: `discBound3 hP hL g : DiscBound3 g`, i.e.
`Φ^d_k(t) ≤ Φ_k(t)`.
* Jensen per product cell (uniform probability on the product cell);
* the one-, two- and three-coordinate marginals of the product of the uniform measures of the cells: `ub`, `ab`, `a3`
  bound the means of `A_1(z_0)`, `A_2(z_0, z_1)`, `A_3(z_{j-2}, z_{j-1}, z_j)` (`TableSound3`);
* the pass: on a product cell the sure edges `{i, i-1}`, `{i, i-2}`, `{i, i-3}` (classes `nf`, `sc`, `tc`) are edges of
  `G = G_1(y(z))`, so `H = seqGraph3 (edgeN ..) (edgeS ..) (edgeT ..) (m + 1) ≤ G`, and the pass value is at most
  `2 Val3 H ≤ 2 g(G)` (`PassSound3`, `Lemma1`).
The pattern of W2's `Disc.lean`, `DiscGraph.lean` and `DiscMeas.lean`.
-/
import W3.Area3
import W3.Interfaces

open MeasureTheory Set Real ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace BHH.W3.Dsc

open BHH BHH.W2 BHH.W3 BHH.W3.Lap

variable {m : ℕ}

/-! ## The three-coordinate marginal of the product of uniform measures -/

/-- three-coordinate marginal (`i, j, l` distinct) -/
lemma integral_unifPi_triple {S : Fin m → Set Pt} (h0 : ∀ j, volume (S j) ≠ 0) (ht : ∀ j, volume (S j) ≠ ⊤)
    {i j l : Fin m} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) {F : Pt × (Pt × Pt) → ℝ} (hF : Measurable F) :
    ∫ z, F (z i, (z j, z l)) ∂unifPi S =
      ((volume (S i)).toReal * (volume (S j)).toReal * (volume (S l)).toReal)⁻¹ *
        ∫ q in S i ×ˢ (S j ×ˢ S l), F q := by
  have hP : ∀ j, IsProbabilityMeasure (unifOn volume (S j)) := fun j => unifOn_isProb (h0 j) (ht j)
  have hPi := unifPi_isProb h0 ht
  have hind : iIndepFun (fun j (z : Fin m → Pt) => z j) (unifPi S) :=
    iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have hmi : (unifPi S).map (fun z => z i) = unifOn volume (S i) := (measurePreserving_eval _ i).map_eq
  have hmj : (unifPi S).map (fun z => z j) = unifOn volume (S j) := (measurePreserving_eval _ j).map_eq
  have hml : (unifPi S).map (fun z => z l) = unifOn volume (S l) := (measurePreserving_eval _ l).map_eq
  -- the pair `(z j, z l)`
  have h2 := (hind.indepFun hjl).map_prod_eq_prod_map_map (measurable_pi_apply j).aemeasurable
    (measurable_pi_apply l).aemeasurable
  rw [hmj, hml] at h2
  -- `z i` is independent of `(z j, z l)`
  have h3 := (hind.indepFun_prodMk (fun k => measurable_pi_apply k) j l i hij.symm hil.symm).symm.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable ((measurable_pi_apply j).prodMk (measurable_pi_apply l)).aemeasurable
  rw [hmi, h2] at h3
  have hin : (unifOn volume (S j)).prod (unifOn volume (S l)) =
      ((volume (S j))⁻¹ * (volume (S l))⁻¹) • volume.restrict (S j ×ˢ S l) := by
    rw [unifOn, unifOn, Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict,
      ← Measure.volume_eq_prod, smul_smul]
  rw [← integral_map ((measurable_pi_apply i).prodMk ((measurable_pi_apply j).prodMk (measurable_pi_apply l))).aemeasurable
    hF.aestronglyMeasurable]
  change ∫ q, F q ∂(unifPi S).map (fun z => (z i, (z j, z l))) = _
  rw [h3, hin, unifOn, Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict,
    ← Measure.volume_eq_prod, smul_smul, integral_smul_measure, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_inv, mul_inv, mul_inv]
  ring

/-! ## The sure edges are edges of `G_1(y(z))` -/

lemma psum_three_sub (z : Fin m → Pt) {b : ℕ} (hb : b + 2 < m) :
    psum z ⟨b + 3, by omega⟩ - psum z ⟨b, by omega⟩ = z ⟨b, by omega⟩ + z ⟨b + 1, by omega⟩ + z ⟨b + 2, hb⟩ := by
  have h1 := psum_succ_sub z hb
  have h2 := psum_two_sub z (show b + 1 < m by omega)
  have e : psum z ⟨b + 3, by omega⟩ - psum z ⟨b, by omega⟩ =
      (psum z ⟨b + 2 + 1, by omega⟩ - psum z ⟨b + 2, by omega⟩) +
        (psum z ⟨b + 2, by omega⟩ - psum z ⟨b, by omega⟩) := by
    abel
  rw [e, h1, h2]
  abel

section Sure

variable {g : GridR} (hNR : 0 < g.NR) (hNT : 0 < g.NT) {D : DiscData3}

/-- the edge `{b+3, b}` -/
lemma unit_adj_three (hD : TableSound3 g D) (c : CellSeq g m) {z : Fin m → Pt}
    (hz : ∀ j, z j ∈ g.cell (c j).1.val (c j).2.val) {b : ℕ} (hb : b + 2 < m)
    (ha : edgeT hNR hNT D c (b + 3) = true) :
    sqDist (psum z ⟨b + 3, by omega⟩) (psum z ⟨b, by omega⟩) ≤ 1 := by
  simp only [edgeT, show 3 ≤ b + 3 by omega, ↓reduceIte, Nat.add_sub_cancel, show b + 3 - 2 = b + 1 by omega,
    show b + 3 - 1 = b + 2 by omega, cget_of_lt hNR hNT c hb, cget_of_lt hNR hNT c (show b < m by omega),
    cget_of_lt hNR hNT c (show b + 1 < m by omega)] at ha
  rw [sqDist_eq_sub, psum_three_sub z hb]
  exact hD.tc _ _ _ _ _ _ (c ⟨b, by omega⟩).1.isLt (c ⟨b + 1, by omega⟩).1.isLt (c ⟨b + 2, hb⟩).1.isLt
    (c ⟨b, by omega⟩).2.isLt (c ⟨b + 1, by omega⟩).2.isLt (c ⟨b + 2, hb⟩).2.isLt ha _ (hz _) _ (hz _) _ (hz _)

/-- the graph of the sure edges is a subgraph of `G_1(y(z))` on the product cell -/
lemma seqGraph3_le_unit (hD : TableSound3 g D) (c : CellSeq g m) {z : Fin m → Pt}
    (hz : ∀ j, z j ∈ g.cell (c j).1.val (c j).2.val) :
    seqGraph3 (edgeN hNR hNT D c) (edgeS hNR hNT D c) (edgeT hNR hNT D c) (m + 1) ≤ unitGraph (psum z) := by
  intro a b hab
  have hne : a ≠ b := fun h => by subst h; exact SimpleGraph.irrefl _ hab
  refine ⟨hne, ?_⟩
  have ha := a.isLt
  have hb := b.isLt
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `a = b + 1`
    have e1 : a = ⟨b.val + 1, by omega⟩ := Fin.ext h1.symm
    rw [e1] at h2 ⊢
    exact unit_adj_one hNR hNT hD.toTableSound c hz (by omega) h2
  · -- `a = b + 2`
    have e1 : a = ⟨b.val + 2, by omega⟩ := Fin.ext h1.symm
    rw [e1] at h2 ⊢
    exact unit_adj_two hNR hNT hD.toTableSound c hz (by omega) h2
  · -- `a = b + 3`
    have e1 : a = ⟨b.val + 3, by omega⟩ := Fin.ext h1.symm
    rw [e1] at h2 ⊢
    exact unit_adj_three hNR hNT hD c hz (by omega) h2
  · -- `b = a + 1`
    have e1 : b = ⟨a.val + 1, by omega⟩ := Fin.ext h1.symm
    rw [e1] at h2 ⊢
    rw [sqDist_comm']
    exact unit_adj_one hNR hNT hD.toTableSound c hz (by omega) h2
  · -- `b = a + 2`
    have e1 : b = ⟨a.val + 2, by omega⟩ := Fin.ext h1.symm
    rw [e1] at h2 ⊢
    rw [sqDist_comm']
    exact unit_adj_two hNR hNT hD.toTableSound c hz (by omega) h2
  · -- `b = a + 3`
    have e1 : b = ⟨a.val + 3, by omega⟩ := Fin.ext h1.symm
    rw [e1] at h2 ⊢
    rw [sqDist_comm']
    exact unit_adj_three hNR hNT hD c hz (by omega) h2

/-- on a product cell, half the pass value of the sure edges is at most `g(G_1(y(z)))` -/
theorem pass_le_dcG3 (hP : PassSound3) (hL : Lemma1) (hD : TableSound3 g D) (c : CellSeq g m) {z : Fin m → Pt}
    (hz : ∀ j, z j ∈ g.cell (c j).1.val (c j).2.val) (hm : 1 ≤ m) :
    (passVal3 (edgeN hNR hNT D c) (edgeS hNR hNT D c) (edgeT hNR hNT D c) (m + 1) : ℝ) / 2 ≤
      dcG (unitGraph (psum z)) := by
  have h1 := hP (edgeN hNR hNT D c) (edgeS hNR hNT D c) (edgeT hNR hNT D c) (m + 1) (by omega)
  have h2 := (hL (m + 1) _ _ (seqGraph3_le_unit hNR hNT hD c hz) (by omega)).2
  linarith

end Sure

/-! ## The mean of `X_3` over a product cell -/

lemma x3_one (z : Fin m → Pt) : x3 z 1 = A2 (zget z 0) (zget z 1) := by
  unfold x3; exact ite_eq_left rfl

lemma x3_of_ne (z : Fin m → Pt) {j : ℕ} (hj : j ≠ 1) :
    x3 z j = A3 (zget z (j - 2)) (zget z (j - 1)) (zget z j) := by
  unfold x3; exact ite_eq_right hj

section Mean

variable {g : GridR} (hNR : 0 < g.NR) (hNT : 0 < g.NT) {D : DiscData3}

/-- the `j`-th term (`j ≥ 1`) of the exponent bound `expoSeq3` -/
def e3 (D : DiscData3) (c : CellSeq g m) (j : ℕ) : ℝ :=
  if j = 1 then
    D.ab (cget hNR hNT c 0).1.val (cget hNR hNT c 1).1.val (doff (cget hNR hNT c 0) (cget hNR hNT c 1))
  else
    D.a3 (cget hNR hNT c (j - 2)).1.val (cget hNR hNT c (j - 1)).1.val (cget hNR hNT c j).1.val
      (doff (cget hNR hNT c (j - 2)) (cget hNR hNT c (j - 1))) (doff (cget hNR hNT c (j - 1)) (cget hNR hNT c j))

lemma expoSeq3_eq (D : DiscData3) (c : CellSeq g m) :
    expoSeq3 hNR hNT D c = D.ub (cget hNR hNT c 0).1.val + ∑ j ∈ Finset.Ico 1 m, e3 hNR hNT D c j := rfl

lemma e3_one (D : DiscData3) (c : CellSeq g m) :
    e3 hNR hNT D c 1 =
      D.ab (cget hNR hNT c 0).1.val (cget hNR hNT c 1).1.val (doff (cget hNR hNT c 0) (cget hNR hNT c 1)) := by
  unfold e3; exact ite_eq_left rfl

lemma e3_of_ne (D : DiscData3) (c : CellSeq g m) {j : ℕ} (hj : j ≠ 1) :
    e3 hNR hNT D c j =
      D.a3 (cget hNR hNT c (j - 2)).1.val (cget hNR hNT c (j - 1)).1.val (cget hNR hNT c j).1.val
        (doff (cget hNR hNT c (j - 2)) (cget hNR hNT c (j - 1))) (doff (cget hNR hNT c (j - 1)) (cget hNR hNT c j)) := by
  unfold e3; exact ite_eq_right hj

/-- the mean of the `j`-th term of `X_3` over a product cell is at most the `j`-th term of the exponent bound -/
lemma integral_x3_le (hD : TableSound3 g D) (c : CellSeq g m) (h0 : ∀ j, volume (cellsOf c j) ≠ 0)
    {j : ℕ} (hj1 : 1 ≤ j) (hjm : j < m) :
    ∫ z, x3 z j ∂unifPi (cellsOf c) ≤ e3 hNR hNT D c j := by
  have ht : ∀ j, volume (cellsOf c j) ≠ ⊤ := fun j => g.volume_cell_ne_top _ _
  have hvpos : ∀ j, 0 < (volume (cellsOf c j)).toReal := fun j => ENNReal.toReal_pos (h0 j) (ht j)
  have hz : ∀ (z : Fin m → Pt) (j : ℕ) (hj : j < m), zget z j = z ⟨j, hj⟩ := fun z j hj => by
    simp [zget, hj]
  by_cases hj : j = 1
  · -- the pair step
    subst hj
    have h0m : 0 < m := by omega
    simp_rw [x3_one]
    rw [e3_one]
    simp_rw [hz _ 0 h0m, hz _ 1 hjm]
    have hne : (⟨0, h0m⟩ : Fin m) ≠ ⟨1, hjm⟩ := by
      intro h; simp only [Fin.mk.injEq] at h; omega
    rw [integral_unifPi_pair h0 ht hne measurable_A2, cget_of_lt hNR hNT c h0m, cget_of_lt hNR hNT c hjm]
    have hab := hD.toTableSound.ab (c ⟨0, h0m⟩).1.val (c ⟨1, hjm⟩).1.val (c ⟨0, h0m⟩).2.val (c ⟨1, hjm⟩).2.val
      (c ⟨0, h0m⟩).1.isLt (c ⟨1, hjm⟩).1.isLt (c ⟨0, h0m⟩).2.isLt (c ⟨1, hjm⟩).2.isLt
    rw [inv_mul_le_iff₀ (mul_pos (hvpos _) (hvpos _))]
    unfold doff
    simp only [cellsOf] at hab ⊢
    linarith [hab]
  · -- the triple steps
    simp_rw [x3_of_ne _ hj]
    rw [e3_of_ne hNR hNT D c hj]
    have hj2 : j - 2 < m := by omega
    have hj1m : j - 1 < m := by omega
    simp_rw [hz _ (j - 2) hj2, hz _ (j - 1) hj1m, hz _ j hjm]
    have hne12 : (⟨j - 2, hj2⟩ : Fin m) ≠ ⟨j - 1, hj1m⟩ := by
      intro h; simp only [Fin.mk.injEq] at h; omega
    have hne13 : (⟨j - 2, hj2⟩ : Fin m) ≠ ⟨j, hjm⟩ := by
      intro h; simp only [Fin.mk.injEq] at h; omega
    have hne23 : (⟨j - 1, hj1m⟩ : Fin m) ≠ ⟨j, hjm⟩ := by
      intro h; simp only [Fin.mk.injEq] at h; omega
    rw [integral_unifPi_triple h0 ht hne12 hne13 hne23 measurable_A3, cget_of_lt hNR hNT c hj2,
      cget_of_lt hNR hNT c hj1m, cget_of_lt hNR hNT c hjm]
    have ha3 := hD.a3 (c ⟨j - 2, hj2⟩).1.val (c ⟨j - 1, hj1m⟩).1.val (c ⟨j, hjm⟩).1.val
      (c ⟨j - 2, hj2⟩).2.val (c ⟨j - 1, hj1m⟩).2.val (c ⟨j, hjm⟩).2.val
      (c ⟨j - 2, hj2⟩).1.isLt (c ⟨j - 1, hj1m⟩).1.isLt (c ⟨j, hjm⟩).1.isLt
      (c ⟨j - 2, hj2⟩).2.isLt (c ⟨j - 1, hj1m⟩).2.isLt (c ⟨j, hjm⟩).2.isLt
    rw [inv_mul_le_iff₀ (mul_pos (mul_pos (hvpos _) (hvpos _)) (hvpos _))]
    unfold doff
    simp only [cellsOf] at ha3 ⊢
    linarith [ha3]

/-- the mean of `X_3` over a product cell is at most the exponent bound of the tables -/
lemma integral_Xsum3_le (hD : TableSound3 g D) (c : CellSeq g m) (hm : 1 ≤ m)
    (h0 : ∀ j, volume (cellsOf c j) ≠ 0) :
    ∫ z, Xsum3 z ∂unifPi (cellsOf c) ≤ expoSeq3 hNR hNT D c := by
  have ht : ∀ j, volume (cellsOf c j) ≠ ⊤ := fun j => g.volume_cell_ne_top _ _
  have hP := unifPi_isProb h0 ht
  have hvpos : ∀ j, 0 < (volume (cellsOf c j)).toReal := fun j => ENNReal.toReal_pos (h0 j) (ht j)
  have hz : ∀ (z : Fin m → Pt) (j : ℕ) (hj : j < m), zget z j = z ⟨j, hj⟩ := fun z j hj => by
    simp [zget, hj]
  have iA1 : Integrable (fun z : Fin m → Pt => A1 (zget z 0)) (unifPi (cellsOf c)) :=
    Integrable.mono' (integrable_const π) (measurable_A1.comp (measurable_zget 0)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (A1_nonneg _)]; exact A1_le_pi _)
  have iX : ∀ j, Integrable (fun z : Fin m → Pt => x3 z j) (unifPi (cellsOf c)) := fun j =>
    Integrable.mono' (integrable_const π) (measurable_x3 j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (x3_nonneg z j)]; exact x3_le_pi z j)
  simp_rw [Xsum3_eq]
  rw [expoSeq3_eq, integral_add iA1 (integrable_finsetSum _ fun j _ => iX j),
    integral_finsetSum _ fun j _ => iX j]
  refine add_le_add ?_ (Finset.sum_le_sum fun j hj => ?_)
  · -- the first step
    have h0m : 0 < m := hm
    simp_rw [hz _ 0 h0m]
    rw [integral_unifPi_eval h0 ht ⟨0, h0m⟩ measurable_A1, cget_of_lt hNR hNT c h0m]
    have hub := hD.toTableSound.ub (c ⟨0, h0m⟩).1.val (c ⟨0, h0m⟩).2.val (c ⟨0, h0m⟩).1.isLt
      (c ⟨0, h0m⟩).2.isLt
    rw [inv_mul_le_iff₀ (hvpos _)]
    simp only [cellsOf] at hub ⊢
    linarith [hub]
  · obtain ⟨hj1, hjm⟩ := Finset.mem_Ico.1 hj
    exact integral_x3_le hNR hNT hD c h0 hj1 hjm

/-! ## One product cell -/

/-- one product cell: Jensen, the marginals and the pass -/
lemma term_le3 (hP : PassSound3) (hL : Lemma1) (hD : TableSound3 g D) (c : CellSeq g m) (hm : 1 ≤ m) {t : ℝ}
    (ht : 0 ≤ t) :
    ENNReal.ofReal (((passVal3 (edgeN hNR hNT D c) (edgeS hNR hNT D c) (edgeT hNR hNT D c) (m + 1) : ℝ) / 2) *
        (∏ j, D.w (c j).1.val) * Real.exp (-(t * expoSeq3 hNR hNT D c))) ≤
      ∫⁻ z in Set.pi univ (cellsOf c), ENNReal.ofReal (dcG (unitGraph (psum z)) * Real.exp (-(t * Xsum3 z))) := by
  set p : ℝ := (passVal3 (edgeN hNR hNT D c) (edgeS hNR hNT D c) (edgeT hNR hNT D c) (m + 1) : ℝ) / 2 with hpdef
  have hp0 : 0 ≤ p := by positivity
  have hw0 : ∀ j, 0 ≤ D.w (c j).1.val := fun j => hD.toTableSound.w_nonneg _
  have ht' : ∀ j, volume (cellsOf c j) ≠ ⊤ := fun j => g.volume_cell_ne_top _ _
  by_cases h0 : ∀ j, volume (cellsOf c j) ≠ 0
  swap
  · -- a cell of measure zero: the term vanishes
    push Not at h0
    obtain ⟨j, hj⟩ := h0
    have hwj : D.w (c j).1.val = 0 := by
      have := hD.toTableSound.w_le (c j).1.val (c j).2.val (c j).1.isLt (c j).2.isLt
      simp only [cellsOf] at hj
      rw [hj, ENNReal.toReal_zero] at this
      exact le_antisymm this (hw0 j)
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hwj, mul_zero, zero_mul, ENNReal.ofReal_zero]
    exact zero_le
  have hP' := unifPi_isProb h0 ht'
  have hmeasΩ : MeasurableSet (Set.pi univ (cellsOf c)) :=
    MeasurableSet.univ_pi fun j => g.measurableSet_cell hNT (c j).2.isLt
  set Ω := Set.pi univ (cellsOf c) with hΩdef
  have hvΩ : volume Ω = ∏ j, volume (cellsOf c j) := volume_pi_set _
  have hvΩt : volume Ω ≠ ⊤ := by rw [hvΩ]; exact ENNReal.prod_ne_top fun j _ => ht' j
  -- integrability of `e^{-tX}`
  have hEm : Measurable fun z : Fin m → Pt => Real.exp (-(t * Xsum3 z)) :=
    Real.measurable_exp.comp ((measurable_Xsum3.const_mul t).neg)
  have hE01 : ∀ z : Fin m → Pt, 0 ≤ Real.exp (-(t * Xsum3 z)) ∧ Real.exp (-(t * Xsum3 z)) ≤ 1 := fun z =>
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by nlinarith [Xsum3_nonneg z])⟩
  have iE : Integrable (fun z => Real.exp (-(t * Xsum3 z))) (unifPi (cellsOf c)) :=
    Integrable.mono' (integrable_const 1) hEm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hE01 z).1]; exact (hE01 z).2)
  have iX : Integrable (Xsum3 (m := m)) (unifPi (cellsOf c)) :=
    Integrable.mono' (integrable_const (π + m * π)) measurable_Xsum3.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Xsum3_nonneg z)]; exact Xsum3_le z)
  -- Jensen
  have hJ : Real.exp (-(t * expoSeq3 hNR hNT D c)) ≤ ∫ z, Real.exp (-(t * Xsum3 z)) ∂unifPi (cellsOf c) := by
    have h1 := exp_integral_le (μ := unifPi (cellsOf c)) (X := fun z => -(t * Xsum3 z)) (iX.const_mul t).neg iE
    have h2 : ∫ z, -(t * Xsum3 z) ∂unifPi (cellsOf c) = -(t * ∫ z, Xsum3 z ∂unifPi (cellsOf c)) := by
      rw [integral_neg, integral_const_mul]
    rw [h2] at h1
    refine le_trans (Real.exp_le_exp.2 ?_) h1
    have := integral_Xsum3_le hNR hNT hD c hm h0
    nlinarith
  -- the volume
  have hvol : ∏ j, D.w (c j).1.val ≤ (volume Ω).toReal := by
    rw [hvΩ, ENNReal.toReal_prod]
    exact Finset.prod_le_prod₀ (fun j _ => hw0 j) fun j _ => hD.toTableSound.w_le _ _ (c j).1.isLt (c j).2.isLt
  -- the integral over the product cell
  have hint : (volume Ω).toReal * Real.exp (-(t * expoSeq3 hNR hNT D c)) ≤
      ∫ z in Ω, Real.exp (-(t * Xsum3 z)) := by
    rw [restrict_pi_eq h0 ht', integral_smul_measure, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hJ ENNReal.toReal_nonneg
  have iEΩ : IntegrableOn (fun z => Real.exp (-(t * Xsum3 z))) Ω := by
    unfold IntegrableOn; rw [restrict_pi_eq h0 ht']; exact iE.smul_measure hvΩt
  calc ENNReal.ofReal (p * (∏ j, D.w (c j).1.val) * Real.exp (-(t * expoSeq3 hNR hNT D c)))
      ≤ ENNReal.ofReal (p * ((volume Ω).toReal * Real.exp (-(t * expoSeq3 hNR hNT D c)))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvol (Real.exp_pos _).le) hp0
    _ ≤ ENNReal.ofReal (p * ∫ z in Ω, Real.exp (-(t * Xsum3 z))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hint hp0)
    _ = ENNReal.ofReal p * ∫⁻ z in Ω, ENNReal.ofReal (Real.exp (-(t * Xsum3 z))) := by
        rw [ENNReal.ofReal_mul hp0, ofReal_integral_eq_lintegral_ofReal iEΩ
          (Filter.Eventually.of_forall fun z => (hE01 z).1)]
    _ = ∫⁻ z in Ω, ENNReal.ofReal (p * Real.exp (-(t * Xsum3 z))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1; ext z; rw [ENNReal.ofReal_mul hp0]
    _ ≤ ∫⁻ z in Ω, ENNReal.ofReal (dcG (unitGraph (psum z)) * Real.exp (-(t * Xsum3 z))) := by
        refine setLIntegral_mono' hmeasΩ fun z hz => ENNReal.ofReal_le_ofReal ?_
        have hzc : ∀ j, z j ∈ g.cell (c j).1.val (c j).2.val := fun j => hz j (Set.mem_univ j)
        exact mul_le_mul_of_nonneg_right (pass_le_dcG3 hNR hNT hP hL hD c hzc hm) (hE01 z).1

end Mean

end BHH.W3.Dsc

namespace BHH.W3

open BHH BHH.W2 BHH.W3.Lap BHH.W3.Dsc

/-- The discretisation bound `Φ^d_k(t) ≤ Φ_k(t)` (Jensen per product cell, marginals of the product of
uniform measures, sure edges, the pass through `PassSound3` and `Lemma1`). -/
theorem discBound3 (hP : PassSound3) (hL : Lemma1) (g : GridR) : DiscBound3 g := by
  intro hNR hNT D hD m hm t ht
  have hm1 : 1 ≤ m := by omega
  set F : (Fin m → Pt) → ℝ≥0∞ := fun z => ENNReal.ofReal (dcG (unitGraph (psum z)) * Real.exp (-(t * Xsum3 z)))
    with hF
  have hmeas : ∀ c : CellSeq g m, MeasurableSet (Set.pi univ (cellsOf c)) := fun c =>
    MeasurableSet.univ_pi fun j => g.measurableSet_cell hNT (c j).2.isLt
  have hdisj : Pairwise (Function.onFun Disjoint fun c : CellSeq g m => Set.pi univ (cellsOf c)) := by
    intro c c' hcc
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ c' j := by
      by_contra h; push Not at h; exact hcc (funext h)
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    have hd := g.cell_disjoint hNT (c j).2.isLt (c' j).2.isLt (ir := (c j).1.val) (ir' := (c' j).1.val)
      (fun he => hj (by
        simp only [Prod.mk.injEq] at he
        exact Prod.ext (Fin.ext he.1) (Fin.ext he.2)))
    exact Set.disjoint_left.1 hd (hz j (Set.mem_univ j)) (hz' j (Set.mem_univ j))
  have hsub : (⋃ c : CellSeq g m, Set.pi univ (cellsOf c)) ⊆ {z : Fin m → Pt | ∀ i, z i ∈ Hp} := by
    intro z hz
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hz
    exact fun i => g.cell_subset_Hp hNT (c i).2.isLt (hc i (Set.mem_univ i))
  have hterm0 : ∀ c : CellSeq g m,
      0 ≤ ((passVal3 (edgeN hNR hNT D c) (edgeS hNR hNT D c) (edgeT hNR hNT D c) (m + 1) : ℝ) / 2) *
        (∏ j, D.w (c j).1.val) * Real.exp (-(t * expoSeq3 hNR hNT D c)) := fun c => by
    have : 0 ≤ ∏ j, D.w (c j).1.val := Finset.prod_nonneg fun j _ => hD.toTableSound.w_nonneg _
    positivity
  unfold Psid3 Psi3
  rw [ENNReal.ofReal_sum_of_nonneg fun c _ => hterm0 c]
  calc ∑ c : CellSeq g m,
        ENNReal.ofReal (((passVal3 (edgeN hNR hNT D c) (edgeS hNR hNT D c) (edgeT hNR hNT D c) (m + 1) : ℝ) / 2) *
          (∏ j, D.w (c j).1.val) * Real.exp (-(t * expoSeq3 hNR hNT D c)))
      ≤ ∑ c : CellSeq g m, ∫⁻ z in Set.pi univ (cellsOf c), F z :=
        Finset.sum_le_sum fun c _ => term_le3 hNR hNT hP hL hD c hm1 ht
    _ = ∫⁻ z in ⋃ c : CellSeq g m, Set.pi univ (cellsOf c), F z := by
        rw [lintegral_iUnion hmeas hdisj F, tsum_fintype]
    _ = ∫⁻ z in ⋃ c : CellSeq g m, Set.pi univ (cellsOf c),
          Set.indicator {z : Fin m → Pt | ∀ i, z i ∈ Hp} F z := by
        refine setLIntegral_congr_fun (MeasurableSet.iUnion hmeas) fun z hz => ?_
        rw [Set.indicator_of_mem (hsub hz)]
    _ ≤ ∫⁻ z, Set.indicator {z : Fin m → Pt | ∀ i, z i ∈ Hp} F z := setLIntegral_le_lintegral _ _

end BHH.W3
