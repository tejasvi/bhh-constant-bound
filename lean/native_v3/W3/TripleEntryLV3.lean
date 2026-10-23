/-
Window-3 entries: `lv3Sound : CosSinTSound → AsinTSound → LV3Sound`.

`LV3LO(ir, ir2, d) = max(π⁻ + euLo(ir2), A(c)⁻ - 2(e0 + e1) - (r_a + r_b + r_c) - 2)` (or the fallback alone) is a lower
bound of the mean of `|B(-z-z') ∪ B(-z') ∪ B(0)|` over `(ir, 0) × (ir2, d)`:
* fallback: the union contains `B(-z') ∪ B(0)` of area `π + A_1(z')`, and `E A_1 ≥ euLo` (T1);
* vertex path: the two-sided vertex lemma at the rounded centroids (`te_lv3_core`), with the union area from
  `unionArea_spec`/`unionSound` (table `cos`/`sin`, `CosSinTSound`), the centroid errors from `distHi` (T4), and the
  distance ranges `hullR`, `hsAt` along the segments (`TripleEntryGeo`).
-/
import W3.TripleEntryGeo

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W3

open BHH BHH.W2 BHH.Cert W2C

/-- `lv3LoF` with the destructuring `let`s replaced by projections (definitionally equal). -/
def te_lv3E (g : Grid) (ir ir2 : ℕ) (d : ℤ) : ℤ :=
  let td := W3C.mkTabData g
  let R1 := td.rings[ir]!
  let R2 := td.rings[ir2]!
  let ch := td.ad.ch
  let fb := piLo + R2.euLo
  let G0 := W3C.geoAt g td.geo ir 0
  let G2 := W3C.geoAt g td.geo ir2 d
  let px0 := Iv.add G0.cx G2.cx
  let py0 := Iv.add G0.cy G2.cy
  let p0x := -(ivMid px0)
  let p0y := -(ivMid py0)
  let p1x := -(ivMid G2.cx)
  let p1y := -(ivMid G2.cy)
  let ep0 := W3C.dist px0 py0 (-p0x) (-p0y)
  let ep1 := W3C.dist G2.cx G2.cy (-p1x) (-p1y)
  match BHH.Cert.unionArea (W3C.cosSinT td.cst) [(p0x, p0y), (p1x, p1y), (0, 0)] ONE W3C.candF with
  | none => fb
  | some ur =>
    match W3C.lvPairT td.atab (W3C.hullR R1 ch (ep0 + ep1 + 1)).1 (W3C.hullR R1 ch (ep0 + ep1 + 1)).2
        (W3C.momentsX [1, 2] [W3C.sqm R1, W3C.sqm R2] (ep0 + ep1)).1
        (W3C.momentsX [1, 2] [W3C.sqm R1, W3C.sqm R2] (ep0 + ep1)).2,
      W3C.lvPairT td.atab (W3C.hsAt td ir ir2 d (ep0 + 1)).1 (W3C.hsAt td ir ir2 d (ep0 + 1)).2
        (W3C.momentsX [1, 1] [W3C.sqm R1, W3C.sqm R2] ep0).1 (W3C.momentsX [1, 1] [W3C.sqm R1, W3C.sqm R2] ep0).2,
      W3C.lvPairT td.atab (W3C.hullR R2 ch (ep1 + 1)).1 (W3C.hullR R2 ch (ep1 + 1)).2
        (W3C.momentsX [0, 1] [W3C.sqm R1, W3C.sqm R2] ep1).1 (W3C.momentsX [0, 1] [W3C.sqm R1, W3C.sqm R2] ep1).2 with
    | some ra, some rb, some rc => Max.max fb (ur.A.lo - 2 * (ep0 + ep1) - (ra + rb + rc) - 2)
    | _, _, _ => fb

lemma te_lv3LoF_eq (g : Grid) (ir ir2 : ℕ) (d : ℤ) : W3C.lv3LoF (W3C.mkTabData g) ir ir2 d = te_lv3E g ir ir2 d :=
  rfl


lemma te_ptsCfg3 (a b c d : ℤ) :
    ptsCfg 3 [(a, b), (c, d), (0, 0)] = ![(fx a, fx b), (fx c, fx d), (0 : Pt)] := by
  funext i; fin_cases i <;> simp [ptsCfg, fx]

set_option maxHeartbeats 4000000 in
/-- D1 (`LV3Sound`): `LV3LO` is a lower bound of the mean of `|B(-z-z') ∪ B(-z') ∪ B(0)|` over `(ir, 0) × (ir2, d)`. -/
theorem lv3Sound (hCS : CosSinTSound) (hAS : AsinTSound) : LV3Sound := by
  intro hG hV g hg ir ir2 d hir hir2 hd
  have hNT := hg.2.2.1
  have h0 : |(0 : ℤ)| < g.NT := by simp only [abs_zero, Nat.cast_pos]; omega
  have h0' : |(0 : ℤ)| ≤ 2 * (g.NT : ℤ) := by simp only [abs_zero]; positivity
  have hd' : |d| ≤ 2 * (g.NT : ℤ) := by have h1 : (0 : ℤ) ≤ (g.NT : ℤ) := Int.natCast_nonneg _; linarith
  have hZm := te_rcell_meas hg ir h0
  have hZ'm := te_rcell_meas hg ir2 hd
  have hZ0 := te_rcell_ne0 hg ir h0
  have hZ'0 := te_rcell_ne0 hg ir2 hd
  have hZt := te_rcell_netop hg ir h0
  have hZ't := te_rcell_netop hg ir2 hd
  have hZb := te_rcell_bdd hg ir h0
  have hZ'b := te_rcell_bdd hg ir2 hd
  have hint : ∀ f : Pt × Pt → ℝ, Continuous f → IntegrableOn f (rcell g ir 0 ×ˢ rcell g ir2 d) :=
    fun f hf => tp_integrableOn_of_bounded (hZb.prod hZ'b) hf
  have hZi : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f (rcell g ir 0) :=
    fun f hf => tp_integrableOn_of_bounded hZb hf
  have hZ'i : ∀ f : Pt → ℝ, Continuous f → IntegrableOn f (rcell g ir2 d) :=
    fun f hf => tp_integrableOn_of_bounded hZ'b hf
  have hSt : volume (rcell g ir 0 ×ˢ rcell g ir2 d) ≠ ⊤ := volume_prod_ne_top hZt hZ't
  have hUint : IntegrableOn (fun p : Pt × Pt => unionArea ![-(p.1 + p.2), -p.2, (0 : Pt)])
      (rcell g ir 0 ×ˢ rcell g ir2 d) := by
    have e : (fun p : Pt × Pt => unionArea ![-(p.1 + p.2), -p.2, (0 : Pt)]) =
        fun p => A2 p.1 p.2 + π + A1 p.1 := funext fun p => te_unionArea_lv3 p.1 p.2
    rw [e]
    have iπ : IntegrableOn (fun _ : Pt × Pt => π) (rcell g ir 0 ×ˢ rcell g ir2 d) := hint _ continuous_const
    exact ((integrableOn_A2 hZt hZ't).add iπ).add (integrableOn_A1_fst hZt hZ't)
  have hVp := te_vr_pos hg ir h0
  have hV'p := te_vr_pos hg ir2 hd
  -- the fallback `π + E u(|z'|)`
  have hfb : fx (piLo + (mkRing g ir2).euLo) * vr g ir 0 * vr g ir2 d ≤
      ∫ p in rcell g ir 0 ×ˢ rcell g ir2 d, unionArea ![-(p.1 + p.2), -p.2, (0 : Pt)] := by
    have iπ : IntegrableOn (fun _ : Pt × Pt => π) (rcell g ir 0 ×ˢ rcell g ir2 d) := hint _ continuous_const
    have iL : IntegrableOn (fun p : Pt × Pt => π + A1 p.2) (rcell g ir 0 ×ˢ rcell g ir2 d) :=
      iπ.add (integrableOn_A1_snd hZt hZ't)
    have hmono := setIntegral_mono_on iL hUint (hZm.prod hZ'm) (fun p _ => te_unionArea_lv3_ge p.1 p.2)
    have hA1 : ∫ z in rcell g ir2 d, A1 z =
        (volume (rcell g ir2 d)).toReal * meanA1 ((gR g).rad ir2) ((gR g).rad (ir2 + 1)) :=
      integral_A1_sector hG a1Radial (te_secOK hg ir2 hd)
    rw [integral_add iπ (integrableOn_A1_snd hZt hZ't), setIntegral_const, measureReal_def, te_vol2,
      setIntegral_snd', hA1, smul_eq_mul] at hmono
    obtain ⟨-, -, -, -, -, heu, -, -⟩ := te_ring hg hir2
    have hpi := piLo_le
    rw [te_fx_add, te_vr_eq, te_vr_eq]
    rw [te_vr_eq] at hVp hV'p
    have hVV := mul_pos hVp hV'p
    nlinarith
  -- the code
  rw [te_lv3LoF_eq]
  unfold te_lv3E
  simp only [show (W3C.mkTabData g).atab = W3C.mkAsinTab from rfl, show (W3C.mkTabData g).cst = W3C.mkCsTab from rfl,
    show (W3C.mkTabData g).ad = mkAData g from rfl, te_rings g hir, te_rings g hir2, te_geoAt g hir h0',
    te_geoAt g hir2 hd']
  split
  · exact hfb
  · next ur hur =>
    split
    · next ra rb rc hra hrb hrc =>
      set G0 := W3C.mkGeo g (mkRing g ir) (mkAData g).ch 0 with hG0
      set G2 := W3C.mkGeo g (mkRing g ir2) (mkAData g).ch d with hG2
      set px0 := G0.cx.add G2.cx with hpx0
      set py0 := G0.cy.add G2.cy with hpy0
      set p0x := -ivMid px0 with hp0x
      set p0y := -ivMid py0 with hp0y
      set p1x := -ivMid G2.cx with hp1x
      set p1y := -ivMid G2.cy with hp1y
      set ep0 := W3C.dist px0 py0 (-p0x) (-p0y) with hep0
      set ep1 := W3C.dist G2.cx G2.cy (-p1x) (-p1y) with hep1
      set c0 : Pt := (fx p0x, fx p0y) with hc0
      set c1 : Pt := (fx p1x, fx p1y) with hc1
      set C := cen (rcell g ir 0) with hC
      set C' := cen (rcell g ir2 d) with hC'
      obtain ⟨hC1, hC2⟩ := te_cen_mem hg hir h0
      obtain ⟨hC'1, hC'2⟩ := te_cen_mem hg hir2 hd
      -- the centroid errors
      have he0 : edist2 (C + C') (-c0) ≤ fx ep0 := by
        have h := TabB.distSound.1 px0 py0 (-p0x) (-p0y) (C + C').1 (C + C').2 (Iv.mem_add hC1 hC'1)
          (Iv.mem_add hC2 hC'2)
        have e1 : ((C + C').1, (C + C').2) = C + C' := rfl
        have e2 : ((fx (-p0x), fx (-p0y)) : Pt) = -c0 := by
          rw [hc0, te_fx_neg p0x, te_fx_neg p0y]; rfl
        rw [e1, e2] at h; exact h
      have he1 : edist2 C' (-c1) ≤ fx ep1 := by
        have h := TabB.distSound.1 G2.cx G2.cy (-p1x) (-p1y) C'.1 C'.2 hC'1 hC'2
        have e2 : ((fx (-p1x), fx (-p1y)) : Pt) = -c1 := by
          rw [hc1, te_fx_neg p1x, te_fx_neg p1y]; rfl
        rw [e2] at h; exact h
      -- the union area at the expansion point
      have hU : fx ur.A.lo ≤ unionArea ![c0, c1, (0 : Pt)] := by
        have h := (unionSound hG (W3C.cosSinT W3C.mkCsTab) hCS W3C.candF 3 _ ur rfl hur).1
        rw [te_ptsCfg3] at h
        exact ivMem_lo_le h
      -- the segments
      have hsa : ∀ p ∈ rcell g ir 0 ×ˢ rcell g ir2 d, ∀ t ∈ Icc (0 : ℝ) 1,
          fx (W3C.hullR (mkRing g ir) (mkAData g).ch (ep0 + ep1 + 1)).1 ≤ enorm2 ((c1 - c0) + t • (p.1 - (c1 - c0))) ∧
          enorm2 ((c1 - c0) + t • (p.1 - (c1 - c0))) ≤ fx (W3C.hullR (mkRing g ir) (mkAData g).ch (ep0 + ep1 + 1)).2 := by
        intro p hp t ht
        have hm : edist2 C (c1 - c0) ≤ fx ep0 + fx ep1 := by
          have e : C - (c1 - c0) = (C + C' - -c0) + -(C' - -c1) := by abel
          rw [← te_enorm2_sub_eq, e]
          refine (te_enorm2_add_le _ _).trans ?_
          rw [te_enorm2_neg, te_enorm2_sub_eq, te_enorm2_sub_eq]
          linarith
        exact te_seg_hullR hg hir h0 hm (E := ep0 + ep1) (by rw [te_fx_add]) p.1 hp.1 t ht
      have hsb : ∀ p ∈ rcell g ir 0 ×ˢ rcell g ir2 d, ∀ t ∈ Icc (0 : ℝ) 1,
          fx (W3C.hsAt (W3C.mkTabData g) ir ir2 d (ep0 + 1)).1 ≤ enorm2 (-c0 + t • ((p.1 + p.2) - -c0)) ∧
          enorm2 (-c0 + t • ((p.1 + p.2) - -c0)) ≤ fx (W3C.hsAt (W3C.mkTabData g) ir ir2 d (ep0 + 1)).2 := by
        intro p hp t ht
        have hm : edist2 C (-c0 - C') ≤ fx ep0 := by
          rw [← te_enorm2_sub_eq, show C - (-c0 - C') = C + C' - -c0 by abel, te_enorm2_sub_eq]; exact he0
        have h0d : |(0 : ℤ) + d| < g.NT := by rwa [zero_add]
        have h := te_seg_hs hg hir hir2 h0 hd h0d hm (E := ep0) le_rfl p.1 hp.1 p.2 (by rw [zero_add]; exact hp.2) t ht
        have e : (-c0 - C' + t • (p.1 - (-c0 - C'))) + (cen (rcell g ir2 (0 + d)) +
            t • (p.2 - cen (rcell g ir2 (0 + d)))) = -c0 + t • ((p.1 + p.2) - -c0) := by
          rw [zero_add]; ext <;> simp <;> ring
        rw [e] at h; exact h
      have hsc : ∀ p ∈ rcell g ir 0 ×ˢ rcell g ir2 d, ∀ t ∈ Icc (0 : ℝ) 1,
          fx (W3C.hullR (mkRing g ir2) (mkAData g).ch (ep1 + 1)).1 ≤ enorm2 (-c1 + t • (p.2 - -c1)) ∧
          enorm2 (-c1 + t • (p.2 - -c1)) ≤ fx (W3C.hullR (mkRing g ir2) (mkAData g).ch (ep1 + 1)).2 := by
        intro p hp t ht
        exact te_seg_hullR hg hir2 hd he1 (E := ep1) le_rfl p.2 hp.2 t ht
      have hcore := te_lv3_core hV hAS hZm hZ'm hint hZi hZ'i hZ0 hZt hZ'0 hZ't hUint
        (te_momHi_nonneg g ir) (te_momHi_nonneg g ir2) (te_mom hg hir h0) (te_mom hg hir2 hd)
        (sqrt_pt_hi _) (sqrt_pt_hi _) he0 he1 hU hra hrb hrc hsa hsb hsc
      -- the vertex value is at most the integral, and so is the fallback
      rw [te_fx_max, mul_assoc, max_mul_of_nonneg _ _ (mul_pos hVp hV'p).le, ← mul_assoc, ← mul_assoc]
      refine max_le hfb ?_
      rw [te_vr_eq, te_vr_eq]
      rw [te_vr_eq] at hVp hV'p
      have hl : fx (ur.A.lo - 2 * (ep0 + ep1) - (ra + rb + rc) - 2) ≤
          fx ur.A.lo - 2 * (fx ep0 + fx ep1) - (fx ra + fx rb + fx rc) := by
        simp only [te_fx_sub, te_fx_add, te_fx_mul_two]
        have : (0 : ℝ) ≤ fx 2 := by unfold fx; positivity
        linarith
      have := mul_le_mul_of_nonneg_right hl (mul_pos hVp hV'p).le
      linarith
    · exact hfb

end BHH.W3
