/-
Window-3 entry primitives: a polar cell lies in the convex hull of its outer pentagon.

The sector `ρ1 < |z| < ρ2`, `α1 < arg z < α2` (`0 < d = α2 - α1 ≤ π/2`, `0 ≤ ρ1`) lies in the convex hull of the inner
corners `ρ1 u(α1)`, `ρ1 u(α2)`, the outer corners `ρ2 u(α1)`, `ρ2 u(α2)` and the apex `(ρ2 / cos(d/2)) u(αm)`,
`αm = (α1 + α2)/2` (where the tangents to the outer arc at its ends meet).  In the coordinates `z = A u(α1) + B u(α2)`
(`A, B ≥ 0`) the point satisfies `A + B ≥ |z| ≥ ρ1` (triangle inequality), `A + B cos d = |z| cos(φ - α1) ≤ ρ2` and
`A cos d + B ≤ ρ2`, and the apex is `k (u(α1) + u(α2))` with `k (1 + cos d) = ρ2`; the point lies on the segment between
its radial multiples on the inner edge and on an edge corner-apex.
Helper lemmas are in the namespace `BHH.W3.Prim`.
-/
import W2.GeoProps
import W2.Euc

open Set Real

noncomputable section

namespace BHH.W3

open BHH BHH.W2

namespace Prim

/-- a point between two of its radial multiples lying in a convex set lies in it -/
lemma mem_of_scaled {C : Set Pt} (hC : Convex ℝ C) {z : Pt} {a l : ℝ} (ha1 : a ≤ 1) (hl : 1 ≤ l)
    (h1 : a • z ∈ C) (h2 : l • z ∈ C) : z ∈ C := by
  rcases eq_or_lt_of_le hl with h | h
  · rw [← h, one_smul] at h2; exact h2
  · have hla : 0 < l - a := by linarith
    have hmem := hC h1 h2 (div_nonneg (by linarith : (0 : ℝ) ≤ l - 1) hla.le)
      (div_nonneg (by linarith : (0 : ℝ) ≤ 1 - a) hla.le) (by field_simp; ring)
    rw [smul_smul, smul_smul, ← add_smul] at hmem
    have e : (l - 1) / (l - a) * a + (1 - a) / (l - a) * l = 1 := by field_simp; ring
    rw [e, one_smul] at hmem
    exact hmem

/-- the pentagon in the coordinates of a pair of vectors `e1, e2` -/
lemma coords_mem_hull (e1 e2 : Pt) {ρ1 ρ2 c k A B : ℝ} (hc : 0 ≤ c) (hkc : k * (1 + c) = ρ2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : ρ1 ≤ A + B) (hs0 : 0 < A + B) (hout1 : A + c * B ≤ ρ2)
    (hout2 : c * A + B ≤ ρ2) :
    A • e1 + B • e2 ∈ convexHull ℝ {ρ1 • e1, ρ1 • e2, ρ2 • e1, ρ2 • e2, k • e1 + k • e2} := by
  set S : Set Pt := {ρ1 • e1, ρ1 • e2, ρ2 • e1, ρ2 • e2, k • e1 + k • e2} with hSdef
  have hconv := convex_convexHull ℝ S
  have m1 : ρ1 • e1 ∈ convexHull ℝ S := subset_convexHull ℝ S (by simp [hSdef])
  have m2 : ρ1 • e2 ∈ convexHull ℝ S := subset_convexHull ℝ S (by simp [hSdef])
  have m3 : ρ2 • e1 ∈ convexHull ℝ S := subset_convexHull ℝ S (by simp [hSdef])
  have m4 : ρ2 • e2 ∈ convexHull ℝ S := subset_convexHull ℝ S (by simp [hSdef])
  have m5 : k • e1 + k • e2 ∈ convexHull ℝ S := subset_convexHull ℝ S (by simp [hSdef])
  -- the radial multiple on the inner edge
  have hin : (ρ1 / (A + B)) • (A • e1 + B • e2) ∈ convexHull ℝ S := by
    have h := hconv m1 m2 (div_nonneg hA hs0.le) (div_nonneg hB hs0.le)
      (by rw [← add_div]; exact div_self hs0.ne')
    convert h using 1
    rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> ring
  have ha1 : ρ1 / (A + B) ≤ 1 := (div_le_one hs0).mpr hs
  rcases le_total B A with hBA | hAB
  · -- the edge from the outer corner `ρ2 e1` to the apex
    have hA0 : 0 < A := by linarith
    have hD : 0 < A + c * B := by nlinarith
    have hout : (ρ2 / (A + c * B)) • (A • e1 + B • e2) ∈ convexHull ℝ S := by
      have h := hconv m3 m5 (div_nonneg (by linarith : 0 ≤ A - B) hD.le)
        (div_nonneg (by nlinarith : 0 ≤ (1 + c) * B) hD.le) (by field_simp; ring)
      convert h using 1
      rw [← hkc]
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul] <;>
        field_simp <;> ring
    exact mem_of_scaled hconv ha1 ((one_le_div hD).mpr hout1) hin hout
  · -- the edge from the outer corner `ρ2 e2` to the apex
    have hB0 : 0 < B := by linarith
    have hD : 0 < c * A + B := by nlinarith
    have hout : (ρ2 / (c * A + B)) • (A • e1 + B • e2) ∈ convexHull ℝ S := by
      have h := hconv m4 m5 (div_nonneg (by linarith : 0 ≤ B - A) hD.le)
        (div_nonneg (by nlinarith : 0 ≤ (1 + c) * A) hD.le) (by field_simp; ring)
      convert h using 1
      rw [← hkc]
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul] <;>
        field_simp <;> ring
    exact mem_of_scaled hconv ha1 ((one_le_div hD).mpr hout2) hin hout

/-- the outer pentagon of the polar cell `(ρ1, ρ2, α1, α2)` -/
def pentPts (ρ1 ρ2 α1 α2 : ℝ) : Set Pt :=
  {(ρ1 * cos α1, ρ1 * sin α1), (ρ1 * cos α2, ρ1 * sin α2), (ρ2 * cos α1, ρ2 * sin α1),
    (ρ2 * cos α2, ρ2 * sin α2),
    (ρ2 / cos ((α2 - α1) / 2) * cos ((α1 + α2) / 2), ρ2 / cos ((α2 - α1) / 2) * sin ((α1 + α2) / 2))}

/-- a polar cell lies in the convex hull of its outer pentagon -/
theorem sector_sub_pentHull {ρ1 ρ2 α1 α2 : ℝ} (hρ1 : 0 ≤ ρ1) (hd1 : α2 - α1 ≤ π / 2) :
    ∀ z ∈ sector ρ1 ρ2 α1 α2, z ∈ convexHull ℝ (pentPts ρ1 ρ2 α1 α2) := by
  rintro _ ⟨⟨ρ, φ⟩, ⟨hρ, hφ⟩, rfl⟩
  simp only [mem_Ioo] at hρ hφ
  rw [polarCoord_symm_apply]
  have hpi := pi_pos
  set d := α2 - α1 with hd
  have hsd : 0 < sin d := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcd : 0 ≤ cos d := cos_nonneg_of_mem_Icc ⟨by linarith, hd1⟩
  have hch : 0 < cos (d / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  set e1 : Pt := (cos α1, sin α1) with he1
  set e2 : Pt := (cos α2, sin α2) with he2
  set A := ρ * sin (α2 - φ) / sin d with hAdef
  set B := ρ * sin (φ - α1) / sin d with hBdef
  set k := ρ2 / cos (d / 2) / (2 * cos (d / 2)) with hkdef
  have hA : 0 ≤ A :=
    div_nonneg (mul_nonneg (by linarith) (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))) hsd.le
  have hB : 0 ≤ B :=
    div_nonneg (mul_nonneg (by linarith) (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))) hsd.le
  -- the point in the basis `u(α1), u(α2)`
  have hz1 : ρ * cos φ = A * cos α1 + B * cos α2 := by
    rw [hAdef, hBdef, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hsd.ne', hd, sin_sub, sin_sub,
      sin_sub]
    ring
  have hz2 : ρ * sin φ = A * sin α1 + B * sin α2 := by
    rw [hAdef, hBdef, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hsd.ne', hd, sin_sub, sin_sub,
      sin_sub]
    ring
  have hzv : ((ρ * cos φ, ρ * sin φ) : Pt) = A • e1 + B • e2 := by
    rw [he1, he2]
    ext
    · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]; exact hz1
    · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]; exact hz2
  -- `A + B ≥ |z| = ρ`
  have hu1 : enorm2 e1 = 1 := by
    rw [he1]; unfold enorm2; rw [cos_sq_add_sin_sq, Real.sqrt_one]
  have hu2 : enorm2 e2 = 1 := by
    rw [he2]; unfold enorm2; rw [cos_sq_add_sin_sq, Real.sqrt_one]
  have hsum : ρ ≤ A + B := by
    have h1 : enorm2 (A • e1 + B • e2) ≤ A + B := by
      calc enorm2 (A • e1 + B • e2) ≤ enorm2 (A • e1) + enorm2 (B • e2) := enorm2_add_le _ _
        _ = A + B := by rw [enorm2_smul, enorm2_smul, abs_of_nonneg hA, abs_of_nonneg hB, hu1, hu2, mul_one, mul_one]
    rw [← hzv, enorm2_polar ρ φ (by linarith)] at h1
    exact h1
  -- the outer constraints
  have hout1 : A + cos d * B ≤ ρ2 := by
    have e : A + cos d * B = ρ * cos (φ - α1) := by
      rw [hd, cos_sub, cos_sub]
      linear_combination (-cos α1) * hz1 + (-sin α1) * hz2 - A * cos_sq_add_sin_sq α1
    rw [e]
    nlinarith [cos_le_one (φ - α1)]
  have hout2 : cos d * A + B ≤ ρ2 := by
    have e : cos d * A + B = ρ * cos (α2 - φ) := by
      rw [hd, cos_sub, cos_sub]
      linear_combination (-cos α2) * hz1 + (-sin α2) * hz2 - B * cos_sq_add_sin_sq α2
    rw [e]
    nlinarith [cos_le_one (α2 - φ)]
  -- the apex
  have hkc : k * (1 + cos d) = ρ2 := by
    have e : cos d = 2 * cos (d / 2) ^ 2 - 1 := by
      rw [← cos_two_mul]; ring_nf
    rw [e, hkdef]
    field_simp
    ring
  have hm1 : α1 = (α1 + α2) / 2 - d / 2 := by rw [hd]; ring
  have hm2 : α2 = (α1 + α2) / 2 + d / 2 := by rw [hd]; ring
  have hc12 : cos α1 + cos α2 = 2 * cos (d / 2) * cos ((α1 + α2) / 2) := by
    have e : cos ((α1 + α2) / 2 - d / 2) + cos ((α1 + α2) / 2 + d / 2) = 2 * cos (d / 2) * cos ((α1 + α2) / 2) := by
      rw [cos_sub, cos_add]; ring
    rw [← hm1, ← hm2] at e
    exact e
  have hs12 : sin α1 + sin α2 = 2 * cos (d / 2) * sin ((α1 + α2) / 2) := by
    have e : sin ((α1 + α2) / 2 - d / 2) + sin ((α1 + α2) / 2 + d / 2) = 2 * cos (d / 2) * sin ((α1 + α2) / 2) := by
      rw [sin_sub, sin_add]; ring
    rw [← hm1, ← hm2] at e
    exact e
  have h5 : ((ρ2 / cos (d / 2) * cos ((α1 + α2) / 2), ρ2 / cos (d / 2) * sin ((α1 + α2) / 2)) : Pt) =
      k • e1 + k • e2 := by
    rw [he1, he2, hkdef]
    ext
    · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      rw [← mul_add, hc12]; field_simp
    · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      rw [← mul_add, hs12]; field_simp
  have hmem := coords_mem_hull (ρ1 := ρ1) e1 e2 hcd hkc hA hB (by linarith) (by linarith) hout1 hout2
  rw [hzv]
  have hset : pentPts ρ1 ρ2 α1 α2 = {ρ1 • e1, ρ1 • e2, ρ2 • e1, ρ2 • e2, k • e1 + k • e2} := by
    unfold pentPts
    rw [← hd, h5]
    rfl
  rw [hset]
  exact hmem

end Prim

end BHH.W3
