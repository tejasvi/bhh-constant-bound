/-
Window-3 entry primitives: the pentagon boxes of `W3C.mkGeo` / `W3C.geoAt` and `TriRangeSound`.

For a relative cell `(ir, j)` (`ir < NR`, `|j| < NT`) the scalar pentagon boxes of `geoAt g (mkTabData g).geo ir j` are
the outward 2^-28 roundings (`box28`) of the interval vertices of `pent` (`cosIvG`/`sinIvG` of the angle intervals
`dθ j`, `dθ (j + 1)`, `dθ (2j + 1)/2`, `Iv.mul`, `Iv.div` by `ch`); they contain the real vertices of the outer pentagon
`pentPts` of the cell (inner and outer corners, apex `r2 / cos(dθ/2)` on the mid direction) provided the division by
`ch ∋ cos(dθ/2)` is valid (`0 < ch.lo`; otherwise `Iv.div` returns `[-1, 1] 2^-PR`).  With `sector_sub_pentHull`
(the cell lies in the hull of `pentPts`) and `triRange28_sound` this gives the two ends of `TriRangeSound` (on the
closures of the convex hulls of the cells, which lie in the closed convex hulls of the pentagons; `0 < ch.lo` is part
of `GridOK`).  Helper lemmas are in the namespace `BHH.W3.Prim`.
-/
import W3.TriplePrimTri
import W3.TriplePrimHull
import W2.TabAngle
import W2.TabRing

open Set Real BHH.Cert

noncomputable section

namespace BHH.W3

open BHH BHH.W2 W2C BHH.W2.TabB

namespace Prim

/-! ## Angle intervals -/

/-- the angle interval `dθ · k` for `|k| ≤ NT` stays inside `(-3π/2, 3π/2)` -/
lemma angK_bounds (g : W2C.Grid) (h2 : 2 ≤ g.NT) (hNT30 : g.NT ≤ 2 ^ 30) (k : ℤ) (hk : |k| ≤ g.NT) :
    -(3 * π / 2) < fx (Iv.mul (dthIv g) (Iv.int k)).lo ∧ fx (Iv.mul (dthIv g) (Iv.int k)).hi < 3 * π / 2 := by
  have hNT : 0 < g.NT := by omega
  have hpi := pi_gt_three'
  have hlo := dth_lo_nonneg g hNT
  have hhi := dth_hi_lt g hNT
  have hNTr : (2 : ℝ) ≤ g.NT := by exact_mod_cast h2
  have hNT30r : (g.NT : ℝ) ≤ 2 ^ 30 := by exact_mod_cast hNT30
  have hph := piHi_pos
  have hlo' : (0 : ℝ) ≤ (dthIv g).lo := by exact_mod_cast hlo
  have hkabs := abs_le.mp hk
  have hk1 : (k : ℝ) ≤ g.NT := by exact_mod_cast hkabs.2
  have hk2 : -(g.NT : ℝ) ≤ k := by
    have h := hkabs.1
    have : (((-(g.NT : ℤ)) : ℤ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  have hHpos : (0 : ℝ) ≤ (piHi : ℝ) / g.NT + 1 := by positivity
  have key : ((piHi : ℝ) / g.NT + 1) * g.NT ≤ piHi + 2 ^ 31 := by
    have e : ((piHi : ℝ) / g.NT + 1) * g.NT = piHi + g.NT := by field_simp
    rw [e]; linarith
  have h2pow : (0 : ℝ) < 2 ^ PR := by positivity
  rcases le_or_gt 0 k with hk0 | hk0
  · rw [mul_int_nonneg hlo hk0]
    simp only
    constructor
    · have h0 : (0 : ℝ) ≤ (((dthIv g).lo * k : ℤ) : ℝ) := by
        push_cast; exact mul_nonneg hlo' (by exact_mod_cast hk0)
      unfold fx
      have : 0 ≤ (((dthIv g).lo * k : ℤ) : ℝ) / 2 ^ PR := div_nonneg h0 h2pow.le
      linarith
    · have hk' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
      have hm : ((dthIv g).hi : ℝ) * (k : ℝ) ≤ ((piHi : ℝ) / g.NT + 1) * g.NT := mul_le_mul hhi.le hk1 hk' hHpos
      have hb : (((dthIv g).hi * k : ℤ) : ℝ) ≤ (piHi : ℝ) + 2 ^ 31 := by push_cast; linarith
      have := fx_lt_four hb
      unfold fx; linarith
  · rw [mul_int_neg hlo hk0]
    simp only
    constructor
    · have hk' : (k : ℝ) < 0 := by exact_mod_cast hk0
      have hm1 : ((piHi : ℝ) / g.NT + 1) * (k : ℝ) ≤ ((dthIv g).hi : ℝ) * (k : ℝ) :=
        mul_le_mul_of_nonpos_right hhi.le hk'.le
      have hm2 : -(((piHi : ℝ) / g.NT + 1) * g.NT) ≤ ((piHi : ℝ) / g.NT + 1) * (k : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hk2 hHpos]
      have hb : -((piHi : ℝ) + 2 ^ 31) ≤ (((dthIv g).hi * k : ℤ) : ℝ) := by push_cast; linarith
      have h4 := fx_lt_four (e := -(((dthIv g).hi * k : ℤ) : ℝ)) (by linarith)
      unfold fx; rw [neg_div] at h4; linarith
    · have hk' : (k : ℝ) < 0 := by exact_mod_cast hk0
      have h0 : (((dthIv g).lo * k : ℤ) : ℝ) ≤ 0 := by
        push_cast; exact mul_nonpos_of_nonneg_of_nonpos hlo' hk'.le
      unfold fx
      have : (((dthIv g).lo * k : ℤ) : ℝ) / 2 ^ PR ≤ 0 := div_nonpos_of_nonpos_of_nonneg h0 h2pow.le
      linarith

/-! ## The geometry table -/

lemma geo_map_get {β : Type*} [Inhabited β] (n : ℕ) (f : ℕ → β) {q : ℕ} (hq : q < n) :
    ((Array.range n).map f)[q]! = f q := by
  rw [getElem!_pos ((Array.range n).map f) q (by simpa using hq)]
  simp

lemma geoAt_eq (g : W2C.Grid) {ir : ℕ} {j : ℤ} (hir : ir < g.NR) (hj : |j| < g.NT) :
    W3C.geoAt g (W3C.mkTabData g).geo ir j = W3C.mkGeo g (mkRing g ir) (mkAData g).ch j := by
  have hgeo : (W3C.mkTabData g).geo = W3C.mkGeoTab g ((Array.range g.NR).map (mkRing g)) (mkAData g).ch := rfl
  unfold W3C.geoAt
  rw [hgeo]
  unfold W3C.mkGeoTab
  dsimp only
  have hjabs := abs_lt.mp hj
  have h2NT : (Int.ofNat (2 * g.NT) : ℤ) = 2 * (g.NT : ℤ) := by simp
  rw [h2NT]
  have hnn : 0 ≤ j + 2 * (g.NT : ℤ) := by omega
  set t := (j + 2 * (g.NT : ℤ)).toNat with ht
  have ht' : (t : ℤ) = j + 2 * g.NT := Int.toNat_of_nonneg hnn
  have htW : t < 4 * g.NT + 1 := by omega
  have hidx : ir * (4 * g.NT + 1) + t < g.NR * (4 * g.NT + 1) := by nlinarith
  rw [geo_map_get _ _ hidx]
  have hdiv : (ir * (4 * g.NT + 1) + t) / (4 * g.NT + 1) = ir := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt htW, zero_add]
  have hmod : (ir * (4 * g.NT + 1) + t) % (4 * g.NT + 1) = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt htW]
  rw [hdiv, hmod, geo_map_get _ _ hir]
  congr 1
  rw [Int.ofNat_eq_natCast, ht']
  simp

/-! ## Boxes of the pentagon vertices -/

/-- the scalar box of an interval point contains the point -/
lemma inBox28_of {x y : ℝ} {vx vy : Iv} (hx : ivMem x vx) (hy : ivMem y vy) :
    inBox28 ((W3C.box28 vx).1, (W3C.box28 vx).2, (W3C.box28 vy).1, (W3C.box28 vy).2) (x, y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have e : PR - W3C.SC = 68 := by unfold PR W3C.SC; norm_num
  have hS : (2 : ℝ) ^ PR = 2 ^ 28 * 2 ^ 68 := by unfold PR; norm_num
  have h68 : (0 : ℝ) < 2 ^ 68 := by positivity
  unfold inBox28 W3C.box28
  simp only
  rw [e]
  rw [hS] at hx1 hx2 hy1 hy2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := shrD_le vx.lo 68
    have : (vx.lo : ℝ) / 2 ^ 68 ≤ x * 2 ^ 28 := by rw [div_le_iff₀ h68]; linarith
    linarith
  · have := le_shrU vx.hi 68
    have : x * 2 ^ 28 ≤ (vx.hi : ℝ) / 2 ^ 68 := by rw [le_div_iff₀ h68]; linarith
    linarith
  · have := shrD_le vy.lo 68
    have : (vy.lo : ℝ) / 2 ^ 68 ≤ y * 2 ^ 28 := by rw [div_le_iff₀ h68]; linarith
    linarith
  · have := le_shrU vy.hi 68
    have : y * 2 ^ 28 ≤ (vy.hi : ℝ) / 2 ^ 68 := by rw [le_div_iff₀ h68]; linarith
    linarith

/-- a vertex of `pent` gives a box of `mkGeo` containing every point of the vertex intervals -/
lemma mem_pv {g : W2C.Grid} {R : Ring} {ch : Iv} {j : ℤ} {P : Iv × Iv} (hP : P ∈ W3C.pent g R ch j)
    {x y : ℝ} (hx : ivMem x P.1) (hy : ivMem y P.2) :
    ∃ p ∈ (W3C.mkGeo g R ch j).pv, inBox28 p (x, y) := by
  refine ⟨((W3C.box28 P.1).1, (W3C.box28 P.1).2, (W3C.box28 P.2).1, (W3C.box28 P.2).2), ?_, inBox28_of hx hy⟩
  unfold W3C.mkGeo
  dsimp only
  exact Array.mem_map.mpr ⟨P, hP, rfl⟩

lemma mem5 {α : Type*} {a b c d e x : α} (h : x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e) :
    x ∈ #[a, b, c, d, e] := by
  rw [Array.mem_def]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact h

/-- the boxes of the cell `(ir, j)` contain the real vertices of its outer pentagon (`0 < ch.lo`) -/
theorem cell_boxes (g : W2C.Grid) (hg : GridOK g) {ir : ℕ} {j : ℤ}
    (hir : ir < g.NR) (hj : |j| < g.NT) :
    ∀ V ∈ pentPts ((gR g).rad ir) ((gR g).rad (ir + 1)) (j * (π / g.NT)) ((j + 1) * (π / g.NT)),
      ∃ p ∈ (W3C.geoAt g (W3C.mkTabData g).geo ir j).pv, inBox28 p V := by
  obtain ⟨h1, h2, hNT2, hNT30, _, _, hch⟩ := hg
  have hNT : 0 < g.NT := by omega
  have hpi := pi_pos
  rw [geoAt_eq g hir hj]
  -- the interval data
  have hr1 : ivMem ((gR g).rad ir) (mkRing g ir).r1 := mem_radIv g h1 h2 ir
  have hr2 : ivMem ((gR g).rad (ir + 1)) (mkRing g ir).r2 := mem_radIv g h1 h2 (ir + 1)
  have hdth := mem_dthIv g hNT
  have hj1 : |j| ≤ g.NT := hj.le
  have hj2 : |j + 1| ≤ g.NT := by
    have := abs_lt.mp hj; rw [abs_le]; constructor <;> omega
  have ha1 : ivMem (j * (π / g.NT)) (Iv.mul (dthIv g) (Iv.int j)) := by
    have := Iv.mem_mul hdth (Iv.mem_int j); rwa [mul_comm] at this
  have ha2 : ivMem ((j + 1) * (π / g.NT)) (Iv.mul (dthIv g) (Iv.int (j + 1))) := by
    have := Iv.mem_mul hdth (Iv.mem_int (j + 1)); rw [mul_comm] at this; push_cast at this; exact this
  obtain ⟨b1l, b1h⟩ := angK_bounds g hNT2 hNT30 j hj1
  obtain ⟨b2l, b2h⟩ := angK_bounds g hNT2 hNT30 (j + 1) hj2
  have hc1 := mem_cosIvG ha1 (by linarith) (by linarith)
  have hs1 := mem_sinIvG ha1 b1l b1h
  have hc2 := mem_cosIvG ha2 (by linarith) (by linarith)
  have hs2 := mem_sinIvG ha2 b2l b2h
  have ham := ang2_mem g hNT j
  obtain ⟨bml, bmh⟩ := ang2_bounds g hNT2 hNT30 j hj
  have hcm := mem_cosIvG ham (by linarith) (by linarith)
  have hsm := mem_sinIvG ham bml bmh
  have hchm : ivMem (Real.cos (π / g.NT / 2)) (mkAData g).ch := (angleSound_of g hNT2 hNT30).1
  have hrA := Iv.mem_div hr2 hchm hch
  -- the apex in the coordinates of `pentPts`
  have ehalf : ((j + 1) * (π / g.NT) - j * (π / g.NT)) / 2 = π / g.NT / 2 := by ring
  have emid : (j * (π / g.NT) + (j + 1) * (π / g.NT)) / 2 = (2 * j + 1) * (π / g.NT) / 2 := by ring
  intro V hV
  unfold pentPts at hV
  rw [ehalf, emid] at hV
  simp only [mem_insert_iff, mem_singleton_iff] at hV
  have hmem : ∀ P ∈ W3C.pent g (mkRing g ir) (mkAData g).ch j, ∀ x y : ℝ, ivMem x P.1 → ivMem y P.2 →
      ∃ p ∈ (W3C.mkGeo g (mkRing g ir) (mkAData g).ch j).pv, inBox28 p (x, y) :=
    fun P hP x y hx hy => mem_pv hP hx hy
  have hpent : W3C.pent g (mkRing g ir) (mkAData g).ch j =
      #[(Iv.mul (mkRing g ir).r1 (cosIvG (Iv.mul (dthIv g) (Iv.int j))),
          Iv.mul (mkRing g ir).r1 (sinIvG (Iv.mul (dthIv g) (Iv.int j)))),
        (Iv.mul (mkRing g ir).r1 (cosIvG (Iv.mul (dthIv g) (Iv.int (j + 1)))),
          Iv.mul (mkRing g ir).r1 (sinIvG (Iv.mul (dthIv g) (Iv.int (j + 1))))),
        (Iv.mul (mkRing g ir).r2 (cosIvG (Iv.mul (dthIv g) (Iv.int j))),
          Iv.mul (mkRing g ir).r2 (sinIvG (Iv.mul (dthIv g) (Iv.int j)))),
        (Iv.mul (mkRing g ir).r2 (cosIvG (Iv.mul (dthIv g) (Iv.int (j + 1)))),
          Iv.mul (mkRing g ir).r2 (sinIvG (Iv.mul (dthIv g) (Iv.int (j + 1))))),
        (Iv.mul (Iv.div (mkRing g ir).r2 (mkAData g).ch)
            (cosIvG (Iv.div2e (Iv.mul (dthIv g) (Iv.int (2 * j + 1))) 1)),
          Iv.mul (Iv.div (mkRing g ir).r2 (mkAData g).ch)
            (sinIvG (Iv.div2e (Iv.mul (dthIv g) (Iv.int (2 * j + 1))) 1)))] := rfl
  rw [hpent] at hmem
  rcases hV with rfl | rfl | rfl | rfl | rfl
  · exact hmem _ (mem5 (Or.inl rfl)) _ _ (Iv.mem_mul hr1 hc1) (Iv.mem_mul hr1 hs1)
  · exact hmem _ (mem5 (Or.inr (Or.inl rfl))) _ _ (Iv.mem_mul hr1 hc2) (Iv.mem_mul hr1 hs2)
  · exact hmem _ (mem5 (Or.inr (Or.inr (Or.inl rfl)))) _ _ (Iv.mem_mul hr2 hc1) (Iv.mem_mul hr2 hs1)
  · exact hmem _ (mem5 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) _ _ (Iv.mem_mul hr2 hc2) (Iv.mem_mul hr2 hs2)
  · exact hmem _ (mem5 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _ _ (Iv.mem_mul hrA hcm) (Iv.mem_mul hrA hsm)

/-- the relative cell `(ir, j)` lies in the convex hull of its outer pentagon -/
theorem rcell_sub_hull (g : W2C.Grid) (hg : GridOK g) (ir : ℕ) (j : ℤ) :
    ∀ z ∈ rcell g ir j, z ∈ convexHull ℝ
      (pentPts ((gR g).rad ir) ((gR g).rad (ir + 1)) (j * (π / g.NT)) ((j + 1) * (π / g.NT))) := by
  obtain ⟨_, _, hNT2, _, _, _, _⟩ := hg
  have hNTr : (2 : ℝ) ≤ g.NT := by exact_mod_cast hNT2
  have hpi := pi_pos
  apply sector_sub_pentHull (rad_nonneg g ir)
  have e : (j + 1) * (π / g.NT) - j * (π / g.NT) = π / g.NT := by ring
  rw [e]
  exact div_le_div_of_nonneg_left hpi.le (by norm_num) hNTr

/-- the closure of the convex hull of a relative cell lies in the convex hull of its outer pentagon (a closed convex
set containing the cell) -/
theorem closure_hull_sub (g : W2C.Grid) (hg : GridOK g) (ir : ℕ) (j : ℤ) :
    closure (convexHull ℝ (rcell g ir j)) ⊆
      convexHull ℝ (pentPts ((gR g).rad ir) ((gR g).rad (ir + 1)) (j * (π / g.NT)) ((j + 1) * (π / g.NT))) := by
  have hfin : (pentPts ((gR g).rad ir) ((gR g).rad (ir + 1)) (j * (π / g.NT)) ((j + 1) * (π / g.NT))).Finite := by
    unfold pentPts
    simp only [Set.finite_insert, Set.finite_singleton]
  exact closure_minimal (convexHull_min (fun z hz => rcell_sub_hull g hg ir j z hz) (convex_convexHull ℝ _))
    (hfin.isClosed_convexHull ℝ)

end Prim

open Prim

/-! ## `TriRangeSound` -/

/-- D7: the pentagon ranges of three relative cells bound `|z_a + z_b + z_c|` on the closures of the convex hulls of
the cells (`0 < ch.lo` is part of `GridOK`). -/
theorem triRangeSound : TriRangeSound := by
  intro g hg ia ib ic dab dbc hia hib hic hdab _ hdac u hu v hv w hw
  have h0 : |(0 : ℤ)| < g.NT := by have := hg.2.2.1; simp; omega
  exact triRange28_sound (cell_boxes g hg hia h0) (cell_boxes g hg hib hdab) (cell_boxes g hg hic hdac)
    (closure_hull_sub g hg ia 0 hu) (closure_hull_sub g hg ib dab hv) (closure_hull_sub g hg ic (dab + dbc) hw)

end BHH.W3
