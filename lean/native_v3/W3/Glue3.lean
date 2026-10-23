/-
Assembly of the window-3 bound from the computational checks of a production run (claims checked by the shards
`W3C.shard3OK`, the t-integral `W2C.tintOK`) and the proof modules of `W3/Interfaces.lean` and the table soundness
`TableSoundOf3`, taken as hypotheses: `sum_C_ge3 : Σ_{k=6}^{kmax} C_k ≥ num/den`.
-/
import W3.Interfaces
import W2.Assembly
import W2.TIntSound

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W3

open W2C BHH.Cert BHH BHH.W2

/-- The checked claims of a production run (both directed recursions agree with every claim). -/
def ClaimsChecked3 (g : Grid) (dtl kmax : ℕ) (cs : List TClaim) : Prop :=
  ∀ c ∈ cs, checkClaims kmax (W3C.runT3 (W3C.mkRun3 g dtl true) true c.1 dtl kmax true).toArray
    (W3C.runT3 (W3C.mkRun3 g dtl true) false c.1 dtl kmax true).toArray c = true

lemma shard3OK_spec {g : Grid} {dtl kmax : ℕ} {cs : List TClaim} (h : W3C.shard3OK g dtl kmax true cs = true) :
    ClaimsChecked3 g dtl kmax cs := by
  unfold W3C.shard3OK at h
  simp only [List.all_eq_true] at h
  exact h

/-- The table soundness of the run data of a grid (the triple entries with W2's pair entries, rotations,
reflections and the index bookkeeping of `W3C.mkPairs`, `W3C.mkTri`). -/
def TableSoundOf3 : Prop :=
  GreenFormula → VertexLemmaSeg → ∀ (g : Grid) (dtl : ℕ), GridOK g → dtl ≤ 48 → g.NT % 2 = 0 →
    nondegOK g = true → TableSound3 (gR g) (discOf3 g dtl)

/-- `Φ^d` is a positive exponential sum (nonnegative weights and exponents). -/
theorem isExpSum_psid3 (g : GridR) (hNR : 0 < g.NR) (hNT : 0 < g.NT) (D : DiscData3) (m : ℕ)
    (hw : ∀ ir, 0 ≤ D.w ir) (hub : ∀ ir, 0 ≤ D.ub ir) (hab : ∀ ir ir2 d, 0 ≤ D.ab ir ir2 d)
    (ha3 : ∀ ia ib ic dab dbc, 0 ≤ D.a3 ia ib ic dab dbc) :
    IsExpSum (fun t => Psid3 g hNR hNT D m t) := by
  classical
  let e := Fintype.equivFin (CellSeq g m)
  refine ⟨Fintype.card (CellSeq g m),
    fun i => ((passVal3 (edgeN hNR hNT D (e.symm i)) (edgeS hNR hNT D (e.symm i)) (edgeT hNR hNT D (e.symm i))
      (m + 1) : ℝ) / 2) * ∏ j, D.w ((e.symm i) j).1.val,
    fun i => expoSeq3 hNR hNT D (e.symm i), fun i => ?_, fun i => ?_, fun t => ?_⟩
  · apply mul_nonneg (by positivity)
    exact Finset.prod_nonneg fun j _ => hw _
  · unfold expoSeq3
    refine add_nonneg (hub _) (Finset.sum_nonneg fun j _ => ?_)
    split_ifs
    · exact hab _ _ _
    · exact ha3 _ _ _ _ _
  · show Psid3 g hNR hNT D m t = _
    unfold Psid3
    refine Fintype.sum_equiv e _ _ (fun c => ?_)
    simp only [Equiv.symm_apply_apply]
    rw [mul_comm t]

lemma toArray_getElem!_eq_getD (l : List (ℕ × ℤ)) (i : ℕ) : l.toArray[i]! = l.getD i (0, 0) := by
  rw [List.getElem!_toArray]
  by_cases h : i < l.length
  · rw [getElem!_pos l i h, List.getD_eq_getElem _ _ h]
  · rw [getElem!_neg l i h, List.getD_eq_default _ _ (by omega)]
    rfl

/-- The claimed enclosures of a checked run bound `Φ^d_k(t_j)` for the data `discOf3`. -/
theorem claim_psid3 (hRec : RecSound3) {g : Grid} {dtl kmax : ℕ} {cs : List TClaim}
    (hsh : ClaimsChecked3 g dtl kmax cs) (hNR : 0 < (gR g).NR) (hNT : 0 < (gR g).NT)
    (h2 : 2 ≤ g.NT) (hev : g.NT % 2 = 0) (hk : 3 ≤ kmax) (hdtl : dtl ≤ 48)
    (hub : ∀ ir : ℕ, 0 ≤ W3C.upq ((W3C.mkTabData g).rings[ir]!).euHi dtl) :
    ∀ c ∈ cs, 1 ≤ c.1 ∧ ∀ e ∈ c.2, 3 ≤ e.1 ∧ e.1 ≤ kmax ∧
      (e.2.1 : ℝ) * 2 ^ (-e.2.2.1) ≤ Psid3 (gR g) hNR hNT (discOf3 g dtl) (e.1 - 1) ((c.1 : ℝ) / 2 ^ dtl) ∧
      Psid3 (gR g) hNR hNT (discOf3 g dtl) (e.1 - 1) ((c.1 : ℝ) / 2 ^ dtl) ≤ (e.2.2.2.1 : ℝ) * 2 ^ (-e.2.2.2.2) := by
  intro c hc
  have hcc := checkClaims_spec (hsh c hc)
  refine ⟨hcc.1, fun e he => ?_⟩
  obtain ⟨hk3, hkm, hlo, hhi⟩ := hcc.2 e he
  obtain ⟨hL, hU⟩ := hRec g dtl kmax c.1 true hNR hNT h2 hev hk hcc.1 hdtl hub e.1 hk3 hkm
  rw [toArray_getElem!_eq_getD] at hlo hhi
  exact ⟨hk3, hkm, hlo.trans hL, hU.trans hhi⟩

lemma discOf3_w_nonneg (g : Grid) (dtl ir : ℕ) : 0 ≤ (discOf3 g dtl).w ir := by
  simp only [discOf3]; positivity

lemma upq_nonneg {a : ℤ} (ha : 0 ≤ a) (dtl : ℕ) : 0 ≤ W3C.upq a dtl := by
  unfold W3C.upq
  have h1 : (0 : ℤ) ≤ (2 ^ dtl - a % 2 ^ dtl) % 2 ^ dtl := Int.emod_nonneg _ (by positivity)
  linarith

lemma discOf3_ab_nonneg (g : Grid) (dtl ir ir2 : ℕ) (d : ℤ) : 0 ≤ (discOf3 g dtl).ab ir ir2 d := by
  simp only [discOf3]
  exact fx_nonneg_of (upq_nonneg (le_max_right _ _) dtl)

lemma discOf3_a3_nonneg (g : Grid) (dtl ia ib ic : ℕ) (dab dbc : ℤ) : 0 ≤ (discOf3 g dtl).a3 ia ib ic dab dbc := by
  simp only [discOf3]; positivity

lemma discOf3_ub_nonneg {g : Grid} {dtl : ℕ} (hub : ∀ ir : ℕ, 0 ≤ W3C.upq ((W3C.mkTabData g).rings[ir]!).euHi dtl)
    (ir : ℕ) : 0 ≤ (discOf3 g dtl).ub ir := by
  simp only [discOf3]
  exact fx_nonneg_of (hub ir)

/-- One `C_k` (`6 ≤ k ≤ kmax`): the Lean t-integral of the claimed enclosures is at most `C_k`. -/
theorem ck_bound3 (hT : TIntBound) (hP : PassSound3) (hL1 : Lemma1) (hLap : ∀ k, LaplaceBound3 k)
    (hD : ∀ (hP : PassSound3) (hL : Lemma1) (g : GridR), DiscBound3 g) (hRec : RecSound3)
    {g : Grid} {dtl T kmax lsub : ℕ} {cs : List TClaim} {L H : Array (Array ℤ)}
    (hNR : 0 < (gR g).NR) (hNT : 0 < (gR g).NT) (h2 : 2 ≤ g.NT) (hev : g.NT % 2 = 0) (hdtl : dtl ≤ 48)
    (hsh : ClaimsChecked3 g dtl kmax cs)
    (hcl : claimLogs (T * 2 ^ dtl) kmax cs = some (L, H))
    (hTS : TableSound3 (gR g) (discOf3 g dtl))
    (hub : ∀ ir : ℕ, 0 ≤ W3C.upq ((W3C.mkTabData g).rings[ir]!).euHi dtl)
    (hntv : 2 ≤ T * 2 ^ dtl) {k : ℕ} (hk6 : 6 ≤ k) (hkm : k ≤ kmax) :
    ENNReal.ofReal (fx (ckLo k dtl (T * 2 ^ dtl) lsub L[k]! H[k]! (logTable (T * 2 ^ dtl * 2 ^ lsub) (dtl + lsub))))
      ≤ C k := by
  set D := discOf3 g dtl with hDdef
  have hexp : IsExpSum (fun t => Psid3 (gR g) hNR hNT D (k - 1) t) :=
    isExpSum_psid3 (gR g) hNR hNT D (k - 1) (discOf3_w_nonneg g dtl) (discOf3_ub_nonneg hub)
      (discOf3_ab_nonneg g dtl) (discOf3_a3_nonneg g dtl)
  obtain ⟨hLs, hHs, hents⟩ := claimLogs_spec hcl k (by omega) hkm
  have hcp := claim_psid3 hRec hsh hNR hNT h2 hev (by omega) hdtl hub
  have hbounds : ∀ j, 1 ≤ j → j ≤ T * 2 ^ dtl →
      0 < Psid3 (gR g) hNR hNT D (k - 1) ((j : ℝ) / 2 ^ dtl) ∧
      fx (L[k]!)[j]! ≤ Real.log (Psid3 (gR g) hNR hNT D (k - 1) ((j : ℝ) / 2 ^ dtl)) ∧
      Real.log (Psid3 (gR g) hNR hNT D (k - 1) ((j : ℝ) / 2 ^ dtl)) ≤ fx (H[k]!)[j]! := by
    intro j hj1 hj2
    obtain ⟨c, hc, e, he, hcj, hek, hlm, hLv, hHv⟩ := hents j hj1 hj2
    obtain ⟨-, -, hlo, hhi⟩ := (hcp c hc).2 e he
    rw [hcj, hek] at hlo hhi
    have hlpos : (0 : ℝ) < (e.2.1 : ℝ) * 2 ^ (-e.2.2.1) := by
      have : (0 : ℝ) < e.2.1 := by exact_mod_cast hlm
      positivity
    have hpos := hlpos.trans_le hlo
    have hhm : 0 < e.2.2.2.1 := by
      by_contra h0
      push_neg at h0
      have : e.2.2.2.1 = 0 := by omega
      rw [this] at hhi
      simp at hhi
      linarith
    refine ⟨hpos, ?_, ?_⟩
    · rw [hLv]
      exact (logScaled_lo hlm _).trans (Real.log_le_log hlpos hlo)
    · rw [hHv]
      exact (Real.log_le_log hpos hhi).trans (logScaled_hi hhm _)
  have hlogs : ∀ i, 1 ≤ i → i ≤ T * 2 ^ dtl * 2 ^ lsub →
      fx (logTable (T * 2 ^ dtl * 2 ^ lsub) (dtl + lsub))[i]! ≤ Real.log ((i : ℝ) / 2 ^ (dtl + lsub)) :=
    fun i hi1 hi2 => logTable_spec _ _ hi1 hi2
  have h1 := hT k dtl (T * 2 ^ dtl) lsub (fun t => Psid3 (gR g) hNR hNT D (k - 1) t) L[k]! H[k]!
    (logTable (T * 2 ^ dtl * 2 ^ lsub) (dtl + lsub)) (by omega) hntv hexp hLs hHs (logTable_size _ _) hbounds hlogs
  have h2' : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (-(π * t))) *
        ENNReal.ofReal (Psid3 (gR g) hNR hNT D (k - 1) t) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (-(π * t))) * Psi3 (k - 1) t := by
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    exact mul_le_mul_right (hD hP hL1 (gR g) hNR hNT D hTS (k - 1) (by omega) t (le_of_lt ht)) _
  exact h1.trans ((mul_le_mul_right h2' _).trans (hLap k (by omega)))

/-- `Σ_{k=6}^{kmax} C_k ≥ num/den` for a production run whose claims and t-integral are checked. -/
theorem sum_C_ge3 (hT : TIntBound) (hP : PassSound3) (hL1 : Lemma1) (hLap : ∀ k, LaplaceBound3 k)
    (hD : ∀ (hP : PassSound3) (hL : Lemma1) (g : GridR), DiscBound3 g) (hRec : RecSound3)
    {g : Grid} {dtl T kmax lsub num den : ℕ} {cs : List TClaim}
    (hNR : 0 < (gR g).NR) (hNT : 0 < (gR g).NT) (h2 : 2 ≤ g.NT) (hev : g.NT % 2 = 0) (hdtl : dtl ≤ 48)
    (hsh : ClaimsChecked3 g dtl kmax cs)
    (htint : tintOK dtl T kmax lsub cs num den = true)
    (hTS : TableSound3 (gR g) (discOf3 g dtl))
    (hub : ∀ ir : ℕ, 0 ≤ W3C.upq ((W3C.mkTabData g).rings[ir]!).euHi dtl)
    (hntv : 2 ≤ T * 2 ^ dtl) :
    ENNReal.ofReal ((num : ℝ) / den) ≤ ∑ k ∈ Finset.Icc 6 kmax, C k := by
  obtain ⟨L, H, hcl, hle⟩ := tintOK_spec htint
  calc ENNReal.ofReal ((num : ℝ) / den)
      ≤ ENNReal.ofReal (∑ k0 ∈ Finset.range (kmax - 5),
          fx (ckLo (k0 + 6) dtl (T * 2 ^ dtl) lsub L[k0 + 6]! H[k0 + 6]!
            (logTable (T * 2 ^ dtl * 2 ^ lsub) (dtl + lsub)))) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ∑ k0 ∈ Finset.range (kmax - 5), ENNReal.ofReal
          (fx (ckLo (k0 + 6) dtl (T * 2 ^ dtl) lsub L[k0 + 6]! H[k0 + 6]!
            (logTable (T * 2 ^ dtl * 2 ^ lsub) (dtl + lsub)))) := ofReal_sum_le' _ _
    _ ≤ ∑ k0 ∈ Finset.range (kmax - 5), C (k0 + 6) := by
        apply Finset.sum_le_sum
        intro k0 hk0
        rw [Finset.mem_range] at hk0
        exact ck_bound3 hT hP hL1 hLap hD hRec hNR hNT h2 hev hdtl hsh hcl hTS hub hntv (by omega) (by omega)
    _ = ∑ k ∈ Finset.Icc 6 kmax, C k := by
        rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
        apply Finset.sum_congr (by congr 1) (fun k0 _ => by rw [add_comm])

end BHH.W3
