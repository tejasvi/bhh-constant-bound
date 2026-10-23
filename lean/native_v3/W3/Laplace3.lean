/-
The Laplace bound: `laplaceBound3 k : LaplaceBound3 k`, i.e.
`C_k ≥ (1/2) ∫_0^∞ t^{k-3/2} e^{-πt} Φ_k(t) dt`.
* sorted coordinates: W2's maps `PS`, `Cσ` and regions `Rσ` (`W2/LapSorted.lean`), here with Dong-Cao's `g` itself,
  which is invariant under relabeling the points (`dcG_iso`: `g` is invariant under graph isomorphisms; the proof of
  `BHH/DomInv.lean` of the window-2 formalization);
* the window-3 area bound `A(y(z)) ≤ π + X_3(z)` (`unionArea_psum_le3`, `W3/Area3.lean`);
* the Gamma integral and Tonelli (the pattern of W2's `LapGamma.lean` and `Laplace.lean`).
-/
import W3.Area3
import W2.LapSorted
import W3.Interfaces

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W3.Lap

open BHH BHH.W2 BHH.W3

/-! ## `g` is invariant under graph isomorphisms -/

lemma degree_eq_natCard' {V : Type*} (G : SimpleGraph V) (v : V) {inst : Fintype (G.neighborSet v)} :
    @SimpleGraph.degree V G v inst = Nat.card (G.neighborSet v) := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, Nat.card_eq_fintype_card]

lemma natCard_neighborSet_iso {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W} (φ : G ≃g G') (v : V) :
    Nat.card (G'.neighborSet (φ v)) = Nat.card (G.neighborSet v) :=
  Nat.card_congr (φ.mapNeighborSet v).symm

/-- the subgraphs induced on the complements of `S` and of its image are isomorphic -/
def induceComplIso {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W} (φ : G ≃g G') (S : Finset V) :
    G.induce ((S : Set V)ᶜ) ≃g G'.induce (((S.map φ.toEquiv.toEmbedding : Finset W) : Set W)ᶜ) where
  toEquiv := φ.toEquiv.subtypeEquiv fun v => by
    simp only [mem_compl_iff, Finset.mem_coe, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  map_rel_iff' := by
    intro a b
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, Equiv.subtypeEquiv_apply,
      RelIso.coe_fn_toEquiv]
    exact φ.map_adj_iff

lemma ccDel_iso {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W} (φ : G ≃g G') (S : Finset V) :
    ccDel G' (S.map φ.toEquiv.toEmbedding) = ccDel G S := by
  unfold ccDel
  exact Nat.card_congr (induceComplIso φ S).connectedComponentEquiv.symm

section Iso

variable {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {G' : SimpleGraph W}

lemma dcD_iso (φ : G ≃g G') : dcD G = dcD G' := by
  unfold dcD
  simp only [degree_eq_natCard']
  congr 1
  exact Fintype.sum_equiv φ.toEquiv _ _ fun v => by
    rw [RelIso.coe_fn_toEquiv, natCard_neighborSet_iso]

lemma n1_iso (φ : G ≃g G') : n1 G = n1 G' := by
  classical
  unfold n1
  simp only [degree_eq_natCard']
  exact Finset.card_equiv φ.toEquiv fun v => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [RelIso.coe_fn_toEquiv, natCard_neighborSet_iso]

lemma dcQ_le_iso (φ : G ≃g G') : dcQ G ≤ dcQ G' := by
  unfold dcQ
  rw [n1_iso φ]
  refine max_le_max le_rfl (Finset.sup'_le _ _ fun S _ => ?_)
  rw [← ccDel_iso φ S, ← Finset.card_map φ.toEquiv.toEmbedding]
  exact Finset.le_sup' (fun T : Finset W => (ccDel G' T : ℤ) - T.card) (Finset.mem_univ _)

lemma dcQ_iso (φ : G ≃g G') : dcQ G = dcQ G' := le_antisymm (dcQ_le_iso φ) (dcQ_le_iso φ.symm)

/-- Dong-Cao's `g` is invariant under graph isomorphisms -/
theorem dcG_iso (φ : G ≃g G') : dcG G = dcG G' := by
  unfold dcG
  by_cases hc : G.Connected
  · rw [ite_eq_left hc, ite_eq_left (φ.connected_iff.mp hc), dcQ_iso φ, dcD_iso φ]
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc (φ.connected_iff.mpr h))]

end Iso

/-- relabeling the vertices by a permutation is a graph isomorphism -/
def comapPermIso {k : ℕ} (G : SimpleGraph (Fin k)) (σ : Equiv.Perm (Fin k)) : G.comap σ ≃g G where
  toEquiv := σ
  map_rel_iff' := Iff.rfl

/-- `g(G_1)` of a relabeled and translated configuration -/
lemma dcG_unitGraph_relabel {k : ℕ} (y : Fin k → Pt) (σ : Equiv.Perm (Fin k)) (c : Pt) :
    dcG (unitGraph (fun j => y (σ j) - c)) = dcG (unitGraph y) := by
  rw [unitGraph_relabel, dcG_iso (comapPermIso _ σ)]

/-! ## Measurability of `g(G_1(y(z)))` -/

variable {m : ℕ}

lemma measurable_dcG_psum : Measurable fun z : Fin m → Pt => dcG (unitGraph (psum z)) := by
  have e : (fun z : Fin m → Pt => dcG (unitGraph (psum z))) = (fun b => dcG (graphB b)) ∘ adjB := by
    funext z; simp only [Function.comp, unitGraph_psum_eq]
  rw [e]
  exact (measurable_of_countable _).comp measurable_adjB

/-! ## Tonelli -/

/-- the Laplace transform of `Φ`: the left-hand side of `LaplaceBound3` as one integral over the increments -/
theorem laplace_lhs_eq3 (k : ℕ) (hk : 3 ≤ k) :
    ENNReal.ofReal (1 / 2) *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (-(π * t))) * Psi3 (k - 1) t =
    ENNReal.ofReal (1 / 2) * ∫⁻ z, Set.indicator {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp}
      (fun z => ENNReal.ofReal (dcG (unitGraph (psum z)) *
        (Real.Gamma ((k : ℝ) - 1 / 2) * (π + Xsum3 z) ^ (-((k : ℝ) - 1 / 2))))) z := by
  congr 1
  set s : ℝ := (k : ℝ) - 1 / 2 with hsdef
  have hs : 0 < s := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hs1 : (k : ℝ) - 3 / 2 = s - 1 := by rw [hsdef]; ring
  have hHm : MeasurableSet {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp} := by
    have : {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp} = ⋂ i, {z | 0 < (z i).1} := by ext z; simp [Hp]
    rw [this]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const ((measurable_pi_apply i).fst)
  -- push the `t`-weight inside the `z`-integral
  set F : ℝ → (Fin (k - 1) → Pt) → ℝ≥0∞ := fun t z => ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (-(π * t))) *
    Set.indicator {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp}
      (fun z => ENNReal.ofReal (dcG (unitGraph (psum z)) * Real.exp (-(t * Xsum3 z)))) z with hFdef
  have h1 : ∀ t, ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (-(π * t))) * Psi3 (k - 1) t =
      ∫⁻ z, F t z := fun t => by
    rw [Psi3, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [h1]
  have hFm : Measurable (Function.uncurry F) := by
    refine Measurable.mul ?_ ?_
    · exact ENNReal.measurable_ofReal.comp ((measurable_fst.pow_const _).mul
        (Real.measurable_exp.comp ((measurable_fst.const_mul π).neg)))
    · refine Measurable.indicator ?_ (measurable_snd hHm)
      exact ENNReal.measurable_ofReal.comp ((measurable_dcG_psum.comp measurable_snd).mul
        (Real.measurable_exp.comp ((measurable_fst.mul (measurable_Xsum3.comp measurable_snd)).neg)))
  rw [lintegral_lintegral_swap hFm.aemeasurable]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp}
  · rw [Set.indicator_of_mem hz]
    have hX0 := Xsum3_nonneg z
    have ha : 0 < π + Xsum3 z := by linarith [Real.pi_pos]
    have hg0 : 0 ≤ dcG (unitGraph (psum z)) := dcG_nonneg _ (by omega)
    calc ∫⁻ t in Ioi (0 : ℝ), F t z
        = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (dcG (unitGraph (psum z))) *
            ENNReal.ofReal (t ^ (s - 1) * Real.exp (-((π + Xsum3 z) * t))) := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
          simp only [hFdef, Set.indicator_of_mem hz]
          rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le),
            ← ENNReal.ofReal_mul hg0, hs1]
          congr 1
          rw [show -((π + Xsum3 z) * t) = -(π * t) + -(t * Xsum3 z) by ring, Real.exp_add]
          ring
      _ = ENNReal.ofReal (dcG (unitGraph (psum z))) * ENNReal.ofReal (Real.Gamma s * (π + Xsum3 z) ^ (-s)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gamma hs ha]
      _ = ENNReal.ofReal (dcG (unitGraph (psum z)) * (Real.Gamma s * (π + Xsum3 z) ^ (-s))) :=
          (ENNReal.ofReal_mul hg0).symm
  · rw [Set.indicator_of_notMem hz]
    have : ∀ t, F t z = 0 := fun t => by simp only [hFdef, Set.indicator_of_notMem hz, mul_zero]
    simp only [this, lintegral_zero]

/-! ## Sorted coordinates -/

/-- `g(G_1(y)) A(y)^{-s}` for the configuration `y = (0, u)` -/
def Gfun3 (s : ℝ) (u : Fin m → Pt) : ℝ := dcG (unitGraph (cfg u)) * unionArea (cfg u) ^ (-s)

lemma Gfun3_PS (s : ℝ) (z : Fin m → Pt) :
    Gfun3 s (PS z) = dcG (unitGraph (psum z)) * unionArea (psum z) ^ (-s) := by
  unfold Gfun3
  rw [cfg_PS]

lemma Gfun3_Cσ (s : ℝ) (σ : Equiv.Perm (Fin (m + 1))) (w : Fin m → Pt) :
    Gfun3 s (Cσ σ w) = dcG (unitGraph (cfg w)) * unionArea (cfg w) ^ (-s) := by
  have hc : cfg (Cσ σ w) = fun j => cfg w (σ j) - cfg w (σ 0) := funext (cfg_Cσ σ w)
  unfold Gfun3
  rw [hc, dcG_unitGraph_relabel, unionArea_relabel]

/-- sorted coordinates: `n! ∫_{H^m} g(G_1(y(z))) A(y(z))^{-s} dz ≤ ∫ g(G_1(y)) A(y)^{-s} dy`, `n = m + 1` -/
theorem sorted_coords3 (s : ℝ) (n : ℕ) (hn : n = m + 1) :
    (n.factorial : ℝ≥0∞) * ∫⁻ z in {z : Fin m → Pt | ∀ i, z i ∈ Hp},
        ENNReal.ofReal (dcG (unitGraph (psum z)) * unionArea (psum z) ^ (-s)) ≤
      ∫⁻ w : Fin m → Pt, ENNReal.ofReal (dcG (unitGraph (cfg w)) * unionArea (cfg w) ^ (-s)) := by
  subst hn
  have hS := measurableSet_Sorted (m := m)
  have h1 : ∫⁻ z in {z : Fin m → Pt | ∀ i, z i ∈ Hp},
      ENNReal.ofReal (dcG (unitGraph (psum z)) * unionArea (psum z) ^ (-s)) =
      ∫⁻ u in Sorted m, ENNReal.ofReal (Gfun3 s u) := by
    have := mp_PS.setLIntegral_comp_preimage_emb memb_PS (fun u => ENNReal.ofReal (Gfun3 s u)) (Sorted m)
    rw [← this, preimage_PS_Sorted]
    simp only [Gfun3_PS]
  have h2 : ∀ σ : Equiv.Perm (Fin (m + 1)), ∫⁻ u in Sorted m, ENNReal.ofReal (Gfun3 s u) =
      ∫⁻ w in Rσ σ, ENNReal.ofReal (dcG (unitGraph (cfg w)) * unionArea (cfg w) ^ (-s)) := by
    intro σ
    have := (mp_Cσ σ).setLIntegral_comp_preimage_emb (memb_Cσ σ) (fun u => ENNReal.ofReal (Gfun3 s u)) (Sorted m)
    rw [← this]
    exact lintegral_congr fun w => by rw [Gfun3_Cσ]
  have hR : ∀ σ : Equiv.Perm (Fin (m + 1)), MeasurableSet (Rσ σ) := fun σ => (mp_Cσ σ).measurable hS
  calc ((m + 1).factorial : ℝ≥0∞) * ∫⁻ z in {z : Fin m → Pt | ∀ i, z i ∈ Hp},
          ENNReal.ofReal (dcG (unitGraph (psum z)) * unionArea (psum z) ^ (-s))
      = ∑ _σ : Equiv.Perm (Fin (m + 1)), ∫⁻ u in Sorted m, ENNReal.ofReal (Gfun3 s u) := by
        rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ σ : Equiv.Perm (Fin (m + 1)),
          ∫⁻ w in Rσ σ, ENNReal.ofReal (dcG (unitGraph (cfg w)) * unionArea (cfg w) ^ (-s)) :=
        Finset.sum_congr rfl fun σ _ => h2 σ
    _ = ∫⁻ w in ⋃ σ, Rσ σ, ENNReal.ofReal (dcG (unitGraph (cfg w)) * unionArea (cfg w) ^ (-s)) := by
        rw [lintegral_iUnion hR Rσ_disjoint, tsum_fintype]
    _ ≤ _ := setLIntegral_le_lintegral _ _

end BHH.W3.Lap

namespace BHH.W3

open BHH BHH.W2 BHH.W3.Lap

/-- The Laplace bound: sorted coordinates, the window-3 area bound, the Laplace transform and Tonelli:
`C_k ≥ (1/2) ∫_0^∞ t^{k-3/2} e^{-πt} Φ_k(t) dt` for `k ≥ 3`. -/
theorem laplaceBound3 (k : ℕ) : LaplaceBound3 k := by
  intro hk
  rw [laplace_lhs_eq3 k hk]
  set s : ℝ := (k : ℝ) - 1 / 2 with hsdef
  have hs : 0 < s := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hG : 0 ≤ Real.Gamma s := (Real.Gamma_pos_of_pos hs).le
  have hHm : MeasurableSet {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp} := by
    have : {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp} = ⋂ i, {z | 0 < (z i).1} := by ext z; simp [Hp]
    rw [this]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const ((measurable_pi_apply i).fst)
  set I := ∫⁻ z in {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp},
    ENNReal.ofReal (dcG (unitGraph (psum z)) * unionArea (psum z) ^ (-s)) with hIdef
  -- the window-3 area bound, pointwise
  have hA : ∫⁻ z, Set.indicator {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp}
      (fun z => ENNReal.ofReal (dcG (unitGraph (psum z)) * (Real.Gamma s * (π + Xsum3 z) ^ (-s)))) z ≤
      ENNReal.ofReal (Real.Gamma s) * I := by
    rw [lintegral_indicator hHm, hIdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z => ?_
    rw [← ENNReal.ofReal_mul hG]
    refine ENNReal.ofReal_le_ofReal ?_
    have hA1 : π ≤ unionArea (psum z) := pi_le_unionArea_psum z
    have hpow : (π + Xsum3 z) ^ (-s) ≤ unionArea (psum z) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by linarith [Real.pi_pos]) (unionArea_psum_le3 z) (by linarith)
    have hg0 : 0 ≤ dcG (unitGraph (psum z)) := dcG_nonneg _ (by omega)
    calc dcG (unitGraph (psum z)) * (Real.Gamma s * (π + Xsum3 z) ^ (-s))
        = Real.Gamma s * (dcG (unitGraph (psum z)) * (π + Xsum3 z) ^ (-s)) := by ring
      _ ≤ Real.Gamma s * (dcG (unitGraph (psum z)) * unionArea (psum z) ^ (-s)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hg0) hG
  -- sorted coordinates
  have hsc := sorted_coords3 (m := k - 1) s k (by omega)
  have hexp : ((k - 1 : ℕ) : ℝ) + 1 - 1 / 2 = s := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), hsdef]; push_cast; ring
  have hJ : ∫⁻ w : Fin (k - 1) → Pt, ENNReal.ofReal (ckIntegrand (k - 1) w) =
      ∫⁻ w : Fin (k - 1) → Pt, ENNReal.ofReal (dcG (unitGraph (cfg w)) * unionArea (cfg w) ^ (-s)) := by
    simp only [ckIntegrand, hexp]
  -- the constants
  have hkf : (0 : ℝ) < k.factorial := Nat.cast_pos.2 (Nat.factorial_pos k)
  have key : ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Real.Gamma s) =
      ENNReal.ofReal (Real.Gamma s / (2 * k.factorial)) * (k.factorial : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc ENNReal.ofReal (1 / 2) * ∫⁻ z, Set.indicator {z : Fin (k - 1) → Pt | ∀ i, z i ∈ Hp}
        (fun z => ENNReal.ofReal (dcG (unitGraph (psum z)) * (Real.Gamma s * (π + Xsum3 z) ^ (-s)))) z
      ≤ ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (Real.Gamma s) * I) := mul_le_mul_right hA _
    _ = ENNReal.ofReal (Real.Gamma s / (2 * k.factorial)) * ((k.factorial : ℝ≥0∞) * I) := by
        rw [← mul_assoc, key, mul_assoc]
    _ ≤ ENNReal.ofReal (Real.Gamma s / (2 * k.factorial)) *
          ∫⁻ w : Fin (k - 1) → Pt, ENNReal.ofReal (dcG (unitGraph (cfg w)) * unionArea (cfg w) ^ (-s)) :=
        mul_le_mul_right hsc _
    _ = C k := by rw [C, hJ]

end BHH.W3
