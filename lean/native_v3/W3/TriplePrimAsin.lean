/-
Window-3 entry primitives: `AsinTSound`, the tabulated `arcsin` bounds `W3C.asinLoT`, `W3C.asinHiT`
(table `W3C.mkAsinTab` of `asinIv` enclosures at the nodes `i 2^-16`, sound by W2's `asinIv_spec`).

`arcsin` is convex on `[0, 1]` (from the concavity of `sin` on `[0, π]`), so it lies below its chords (`asinHiT`, chord
through the upper table values) and above the extensions of its secants beyond the right node (`asinLoT`, slope bounded
below by `max(lo_i - hi_{i-1}, 0) / h`); `x ≤ arcsin x` on `[0, 1]` (first cell); exact `asinIv` in the steep zone;
`π/2` beyond `1`.
Helper lemmas are in the namespace `BHH.W3.Prim`.
-/
import W3.Interfaces
import W2.FixSound

open Set Real BHH.Cert

noncomputable section

namespace BHH.W3

open BHH BHH.W2

namespace Prim

/-! ## Convexity of `arcsin` on `[0, 1]` -/

/-- `arcsin` is convex on `[0, 1]` -/
lemma convexOn_arcsin_Icc : ConvexOn ℝ (Icc (0 : ℝ) 1) Real.arcsin := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hpi := Real.pi_pos
  have hα0 : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.mpr hx.1
  have hα1 : Real.arcsin x ≤ π / 2 := Real.arcsin_le_pi_div_two x
  have hβ0 : 0 ≤ Real.arcsin y := Real.arcsin_nonneg.mpr hy.1
  have hβ1 : Real.arcsin y ≤ π / 2 := Real.arcsin_le_pi_div_two y
  have h1 := strictConcaveOn_sin_Icc.concaveOn.2 (⟨hα0, by linarith⟩ : Real.arcsin x ∈ Icc 0 π)
    (⟨hβ0, by linarith⟩ : Real.arcsin y ∈ Icc 0 π) ha hb hab
  simp only [smul_eq_mul] at h1
  rw [Real.sin_arcsin (by linarith [hx.1]) hx.2, Real.sin_arcsin (by linarith [hy.1]) hy.2] at h1
  have hm0 : 0 ≤ a * Real.arcsin x + b * Real.arcsin y := by positivity
  have hm1 : a * Real.arcsin x + b * Real.arcsin y ≤ π / 2 := by
    have e1 := mul_le_mul_of_nonneg_left hα1 ha
    have e2 := mul_le_mul_of_nonneg_left hβ1 hb
    have key : a * (π / 2) + b * (π / 2) = π / 2 := by rw [← add_mul, hab, one_mul]
    linarith
  calc Real.arcsin (a * x + b * y) ≤ Real.arcsin (Real.sin (a * Real.arcsin x + b * Real.arcsin y)) :=
        Real.arcsin_le_arcsin h1
    _ = a * Real.arcsin x + b * Real.arcsin y := Real.arcsin_sin (by linarith) hm1

/-- the chord of `arcsin` over `[x0, x1] ⊆ [0, 1]` lies above it -/
lemma arcsin_le_chord {x0 x1 x : ℝ} (h0 : 0 ≤ x0) (h01 : x0 < x1) (h1 : x1 ≤ 1) (hx0 : x0 ≤ x) (hx1 : x ≤ x1) :
    Real.arcsin x ≤ Real.arcsin x0 + (Real.arcsin x1 - Real.arcsin x0) * ((x - x0) / (x1 - x0)) := by
  have hd : 0 < x1 - x0 := by linarith
  set t := (x - x0) / (x1 - x0) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hxe : x = (1 - t) * x0 + t * x1 := by
    rw [ht]
    field_simp
    ring
  have hc := convexOn_arcsin_Icc.2 (⟨h0, by linarith⟩ : x0 ∈ Icc (0 : ℝ) 1) (⟨by linarith, h1⟩ : x1 ∈ Icc (0 : ℝ) 1)
    (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at hc
  rw [← hxe] at hc
  linarith

/-- the secant of `arcsin` through `x0 < x1` (in `[0, 1]`), extended beyond `x1`, lies below it on `[x1, 1]` -/
lemma secant_le_arcsin {x0 x1 x : ℝ} (h0 : 0 ≤ x0) (h01 : x0 < x1) (hx1 : x1 ≤ x) (hx : x ≤ 1) :
    Real.arcsin x1 + (Real.arcsin x1 - Real.arcsin x0) / (x1 - x0) * (x - x1) ≤ Real.arcsin x := by
  rcases eq_or_lt_of_le hx1 with h | h
  · subst h; simp
  · have hs := convexOn_arcsin_Icc.slope_mono_adjacent (⟨h0, by linarith⟩ : x0 ∈ Icc (0 : ℝ) 1)
      (⟨by linarith, hx⟩ : x ∈ Icc (0 : ℝ) 1) h01 h
    have hd : 0 < x - x1 := by linarith
    rw [le_div_iff₀ hd] at hs
    linarith

/-- `x ≤ arcsin x` for `0 ≤ x ≤ 1` -/
lemma le_arcsin_self {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ≤ Real.arcsin x := by
  have hs := Real.sin_le (Real.arcsin_nonneg.mpr h0)
  rwa [Real.sin_arcsin (by linarith) h1] at hs

/-! ## The table -/

lemma map_range_get! {β : Type*} [Inhabited β] (n : ℕ) (f : ℕ → β) {q : ℕ} (hq : q < n) :
    ((Array.range n).map f)[q]! = f q := by
  rw [getElem!_pos ((Array.range n).map f) q (by simpa using hq)]
  simp

lemma HAK_eq : W3C.HAK = 2 ^ 80 := by unfold W3C.HAK PR W3C.AK; norm_num

lemma ONE_eq_HAK : ONE = 2 ^ 16 * W3C.HAK := by rw [HAK_eq]; unfold ONE; norm_num

lemma mkAsinTab_get {n : ℕ} (hn : n ≤ 2 ^ 16) :
    W3C.mkAsinTab[n]! = W2C.asinIv (Iv.pt (Int.ofNat n * W3C.HAK)) := by
  unfold W3C.mkAsinTab
  rw [map_range_get! _ _ (by unfold W3C.AK; omega)]
  rfl

/-- the table node `n 2^-16` -/
lemma fx_node (n : ℕ) : fx (Int.ofNat n * W3C.HAK) = (n : ℝ) / 2 ^ 16 := by
  rw [HAK_eq]
  unfold fx PR
  simp only [Int.ofNat_eq_natCast]
  push_cast
  field_simp
  try ring

lemma asinTab_hi {n : ℕ} (hn : n ≤ 2 ^ 16) :
    Real.arcsin ((n : ℝ) / 2 ^ 16) ≤ fx (W3C.mkAsinTab[n]!).hi := by
  rw [mkAsinTab_get hn, ← fx_node]
  exact ivMem_hi_le (asinIv_spec (Iv.mem_pt _))

lemma asinTab_lo {n : ℕ} (hn : n ≤ 2 ^ 16) :
    fx (W3C.mkAsinTab[n]!).lo ≤ Real.arcsin ((n : ℝ) / 2 ^ 16) := by
  rw [mkAsinTab_get hn, ← fx_node]
  exact ivMem_lo_le (asinIv_spec (Iv.mem_pt _))

/-! ## The cell of an argument -/

/-- the cell `i = ⌊a / h⌋` of `a ∈ (0, 0.98·2^PR)` and the offset `fr = a - i h ∈ [0, h)` -/
lemma cell_facts {a : ℤ} (ha0 : 0 < a) (ha1 : 50 * a < 49 * ONE) :
    0 ≤ a / W3C.HAK ∧ a / W3C.HAK + 1 ≤ 2 ^ 16 ∧ 0 ≤ a - a / W3C.HAK * W3C.HAK ∧
      a - a / W3C.HAK * W3C.HAK < W3C.HAK := by
  have hh : (0 : ℤ) < W3C.HAK := by rw [HAK_eq]; norm_num
  have hdiv := Int.mul_ediv_add_emod a W3C.HAK
  have hm0 := Int.emod_nonneg a hh.ne'
  have hm1 := Int.emod_lt_of_pos a hh
  have hi0 : 0 ≤ a / W3C.HAK := Int.ediv_nonneg ha0.le hh.le
  have hO := ONE_eq_HAK
  refine ⟨hi0, ?_, ?_, ?_⟩
  · -- i h ≤ a < (49/50) 2^16 h
    have h1 : a / W3C.HAK * W3C.HAK ≤ a := Int.ediv_mul_le a hh.ne'
    have h2 : 50 * (a / W3C.HAK * W3C.HAK) < 49 * (2 ^ 16 * W3C.HAK) := by rw [← hO]; linarith
    have h3 : (50 * (a / W3C.HAK)) * W3C.HAK < (49 * 2 ^ 16) * W3C.HAK := by linarith
    have h4 : 50 * (a / W3C.HAK) < 49 * 2 ^ 16 := lt_of_mul_lt_mul_right h3 hh.le
    omega
  · linarith [mul_comm W3C.HAK (a / W3C.HAK)]
  · linarith [mul_comm W3C.HAK (a / W3C.HAK)]

/-! ## The bounds -/

lemma fx_ONE' : fx ONE = 1 := by
  unfold fx; rw [ONE_cast]; exact div_self (ne_of_gt SC_pos)

lemma fx_add' (a b : ℤ) : fx (a + b) = fx a + fx b := by unfold fx; push_cast; ring

lemma fx_sub' (a b : ℤ) : fx (a - b) = fx a - fx b := by unfold fx; push_cast; ring

lemma fx_max' (a b : ℤ) : fx (max a b) = max (fx a) (fx b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (fx_le_iff.mpr h)]
  · rw [max_eq_left h, max_eq_left (fx_le_iff.mpr h)]

theorem asinHiT_spec (a : ℤ) : Real.arcsin (fx a) ≤ fx (W3C.asinHiT W3C.mkAsinTab a) := by
  unfold W3C.asinHiT
  dsimp only
  split_ifs with h1 h2 h3
  · exact le_trans (Real.arcsin_le_pi_div_two _) le_halfPiHi
  · -- a ≤ 0: arcsin (fx a) ≤ arcsin 0 ≤ table value at 0
    have := asinTab_hi (n := 0) (by norm_num)
    simp only [Nat.cast_zero, zero_div] at this
    refine le_trans (Real.arcsin_le_arcsin ?_) this
    have : fx a ≤ fx 0 := fx_le_iff.mpr h2
    simpa [fx] using this
  · exact ivMem_hi_le (asinIv_spec (Iv.mem_pt a))
  · have h2' := not_le.mp h2
    have h3' := not_le.mp h3
    obtain ⟨hi0, hi1, hfr0, hfr1⟩ := cell_facts h2' h3'
    set h := W3C.HAK with hhdef
    set i := a / h with hidef
    have hh : (0 : ℤ) < h := by rw [hhdef, HAK_eq]; norm_num
    have hhr : (0 : ℝ) < h := by exact_mod_cast hh
    -- the nodes
    have hn0 : (i.toNat : ℕ) ≤ 2 ^ 16 := by omega
    have hn1 : ((i + 1).toNat : ℕ) ≤ 2 ^ 16 := by omega
    have hA0 := asinTab_hi hn0
    have hA1 := asinTab_hi hn1
    have ec0 : ((i.toNat : ℕ) : ℝ) = (i : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hi0
    have ec1 : (((i + 1).toNat : ℕ) : ℝ) = (i : ℝ) + 1 := by
      have : (((i + 1).toNat : ℕ) : ℤ) = i + 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [ec0] at hA0
    rw [ec1] at hA1
    -- real positions: x_i = i/2^16, x = fx a, x_{i+1} = (i+1)/2^16, h = 2^80
    have hh80 : (h : ℝ) = 2 ^ 80 := by rw [hhdef, HAK_eq]; norm_num
    have hfa : fx a = (i : ℝ) / 2 ^ 16 + ((a - i * h : ℤ) : ℝ) / 2 ^ 96 := by
      unfold fx PR
      push_cast
      rw [hh80]
      field_simp
      ring
    have hfr0r : (0 : ℝ) ≤ ((a - i * h : ℤ) : ℝ) := by exact_mod_cast hfr0
    have hfr1r : ((a - i * h : ℤ) : ℝ) < h := by exact_mod_cast hfr1
    have hx0 : (i : ℝ) / 2 ^ 16 ≤ fx a := by
      rw [hfa]
      have : (0:ℝ) ≤ ((a - i * h : ℤ) : ℝ) / 2 ^ 96 := by positivity
      linarith
    have hx1 : fx a ≤ ((i : ℝ) + 1) / 2 ^ 16 := by
      rw [hfa]
      have : ((a - i * h : ℤ) : ℝ) / 2 ^ 96 ≤ 1 / 2 ^ 16 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        rw [hh80] at hfr1r
        nlinarith
      rw [add_div]
      linarith
    have hi0r : (0 : ℝ) ≤ (i : ℝ) / 2 ^ 16 := by
      have : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi0
      positivity
    have hi1r : ((i : ℝ) + 1) / 2 ^ 16 ≤ 1 := by
      have : ((i : ℝ) + 1) ≤ 2 ^ 16 := by exact_mod_cast hi1
      rw [div_le_one (by positivity)]
      exact this
    have hlt : (i : ℝ) / 2 ^ 16 < ((i : ℝ) + 1) / 2 ^ 16 := by
      apply div_lt_div_of_pos_right _ (by positivity); linarith
    have hch := arcsin_le_chord hi0r hlt hi1r hx0 hx1
    -- the weight λ = fr / h
    have hlam : (fx a - (i : ℝ) / 2 ^ 16) / (((i : ℝ) + 1) / 2 ^ 16 - (i : ℝ) / 2 ^ 16) =
        ((a - i * h : ℤ) : ℝ) / h := by
      rw [hfa, hh80]
      field_simp
      ring
    rw [hlam] at hch
    have hl0 : (0 : ℝ) ≤ ((a - i * h : ℤ) : ℝ) / h := div_nonneg hfr0r hhr.le
    have hl1 : ((a - i * h : ℤ) : ℝ) / h ≤ 1 := (div_le_one hhr).mpr hfr1r.le
    -- (1 - λ) A0 + λ A1 ≤ (1 - λ) H0 + λ H1
    set hi0v := (W3C.mkAsinTab[i.toNat]!).hi
    set hi1v := (W3C.mkAsinTab[(i + 1).toNat]!).hi
    have hb : Real.arcsin ((i : ℝ) / 2 ^ 16) + (Real.arcsin (((i : ℝ) + 1) / 2 ^ 16) -
        Real.arcsin ((i : ℝ) / 2 ^ 16)) * (((a - i * h : ℤ) : ℝ) / h) ≤
        fx hi0v + (fx hi1v - fx hi0v) * (((a - i * h : ℤ) : ℝ) / h) := by
      have e1 := mul_le_mul_of_nonneg_left hA0 (by linarith : (0 : ℝ) ≤ 1 - ((a - i * h : ℤ) : ℝ) / h)
      have e2 := mul_le_mul_of_nonneg_left hA1 hl0
      nlinarith
    have hround := le_divU ((hi1v - hi0v) * (a - i * h)) h hh
    have hfin : fx hi0v + (fx hi1v - fx hi0v) * (((a - i * h : ℤ) : ℝ) / h) ≤
        fx (hi0v + divU ((hi1v - hi0v) * (a - i * h)) h) := by
      have e : (fx hi1v - fx hi0v) * (((a - i * h : ℤ) : ℝ) / h) =
          (((hi1v - hi0v) * (a - i * h) : ℤ) : ℝ) / h / 2 ^ PR := by
        unfold fx; push_cast; field_simp
      have hr2 : (((hi1v - hi0v) * (a - i * h) : ℤ) : ℝ) / h / 2 ^ PR ≤
          fx (divU ((hi1v - hi0v) * (a - i * h)) h) := by
        unfold fx; exact div_le_div_of_nonneg_right hround (by positivity)
      rw [fx_add', e]
      linarith
    linarith

theorem asinLoT_spec (a : ℤ) (ha : 0 ≤ a) : fx (W3C.asinLoT W3C.mkAsinTab a) ≤ Real.arcsin (fx a) := by
  unfold W3C.asinLoT
  dsimp only
  split_ifs with h1 h2 h3 h4
  · -- 1 ≤ x: table value at 1 ≤ π/2 = arcsin x
    have := asinTab_lo (n := 2 ^ 16) le_rfl
    have e : ((2 ^ 16 : ℕ) : ℝ) / 2 ^ 16 = 1 := by norm_num
    rw [e, Real.arcsin_one] at this
    have hx : 1 ≤ fx a := by
      have := fx_le_iff.mpr h1
      rwa [fx_ONE'] at this
    rw [Real.arcsin_of_one_le hx]
    simpa [W3C.AK] using this
  · -- a = 0
    have ha0 : a = 0 := le_antisymm h2 ha
    subst ha0
    simp [fx]
  · exact ivMem_lo_le (asinIv_spec (Iv.mem_pt a))
  · -- first cell: x ≤ arcsin x
    have h1' := not_le.mp h1
    have h2' := not_le.mp h2
    have hx1 : fx a ≤ 1 := by
      have := fx_le_iff.mpr h1'.le
      rwa [fx_ONE'] at this
    exact le_arcsin_self (fx_nonneg_iff.mpr h2'.le) hx1
  · have h1' := not_le.mp h1
    have h2' := not_le.mp h2
    have h3' := not_le.mp h3
    have hi0' : ¬ (a / W3C.HAK = 0) := by simpa using h4
    obtain ⟨hi0, hi1, hfr0, hfr1⟩ := cell_facts h2' h3'
    set h := W3C.HAK with hhdef
    set i := a / h with hidef
    have hipos : 1 ≤ i := by omega
    have hh : (0 : ℤ) < h := by rw [hhdef, HAK_eq]; norm_num
    have hhr : (0 : ℝ) < h := by exact_mod_cast hh
    have hn0 : ((i - 1).toNat : ℕ) ≤ 2 ^ 16 := by omega
    have hn1 : (i.toNat : ℕ) ≤ 2 ^ 16 := by omega
    have hH0 := asinTab_hi hn0
    have hL1 := asinTab_lo hn1
    have ec0 : (((i - 1).toNat : ℕ) : ℝ) = (i : ℝ) - 1 := by
      have : (((i - 1).toNat : ℕ) : ℤ) = i - 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have ec1 : ((i.toNat : ℕ) : ℝ) = (i : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hi0
    rw [ec0] at hH0
    rw [ec1] at hL1
    have hh80 : (h : ℝ) = 2 ^ 80 := by rw [hhdef, HAK_eq]; norm_num
    have hfa : fx a = (i : ℝ) / 2 ^ 16 + ((a - i * h : ℤ) : ℝ) / 2 ^ 96 := by
      unfold fx PR
      push_cast
      rw [hh80]
      field_simp
      ring
    have hfr0r : (0 : ℝ) ≤ ((a - i * h : ℤ) : ℝ) := by exact_mod_cast hfr0
    have hx0 : (i : ℝ) / 2 ^ 16 ≤ fx a := by
      rw [hfa]; have : (0:ℝ) ≤ ((a - i * h : ℤ) : ℝ) / 2 ^ 96 := by positivity
      linarith
    have hx1 : fx a ≤ 1 := by
      have := fx_le_iff.mpr h1'.le
      rwa [fx_ONE'] at this
    have hir : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hipos
    have hm0 : (0 : ℝ) ≤ ((i : ℝ) - 1) / 2 ^ 16 := by
      apply div_nonneg _ (by positivity); linarith
    have hlt : ((i : ℝ) - 1) / 2 ^ 16 < (i : ℝ) / 2 ^ 16 := by
      apply div_lt_div_of_pos_right _ (by positivity); linarith
    have hsec := secant_le_arcsin hm0 hlt hx0 hx1
    -- slope ≥ max(L1 - H0, 0) / h (scaled)
    set lo1 := (W3C.mkAsinTab[i.toNat]!).lo
    set hi0v := (W3C.mkAsinTab[(i - 1).toNat]!).hi
    have hdx : (i : ℝ) / 2 ^ 16 - ((i : ℝ) - 1) / 2 ^ 16 = 1 / 2 ^ 16 := by ring
    have hD : max (fx lo1 - fx hi0v) 0 ≤
        Real.arcsin ((i : ℝ) / 2 ^ 16) - Real.arcsin (((i : ℝ) - 1) / 2 ^ 16) :=
      max_le (by linarith) (by linarith [Real.arcsin_le_arcsin hlt.le])
    have hslope : fx (max (lo1 - hi0v) 0) * 2 ^ 16 ≤
        (Real.arcsin ((i : ℝ) / 2 ^ 16) - Real.arcsin (((i : ℝ) - 1) / 2 ^ 16)) /
        ((i : ℝ) / 2 ^ 16 - ((i : ℝ) - 1) / 2 ^ 16) := by
      rw [fx_max', fx_sub', show fx 0 = 0 by simp [fx], hdx, div_div_eq_mul_div, div_one]
      exact mul_le_mul_of_nonneg_right hD (by positivity)
    -- x - x_i = fr / 2^96
    have hxd : fx a - (i : ℝ) / 2 ^ 16 = ((a - i * h : ℤ) : ℝ) / 2 ^ 96 := by rw [hfa]; ring
    have hlow : fx lo1 + fx (max (lo1 - hi0v) 0) * 2 ^ 16 * (((a - i * h : ℤ) : ℝ) / 2 ^ 96) ≤
        Real.arcsin (fx a) := by
      rw [hxd] at hsec
      have e1 := mul_le_mul_of_nonneg_right hslope (by positivity : (0 : ℝ) ≤ ((a - i * h : ℤ) : ℝ) / 2 ^ 96)
      linarith
    have hround := divD_le (max (lo1 - hi0v) 0 * (a - i * h)) h hh
    have hfin : fx (lo1 + divD (max (lo1 - hi0v) 0 * (a - i * h)) h) ≤
        fx lo1 + fx (max (lo1 - hi0v) 0) * 2 ^ 16 * (((a - i * h : ℤ) : ℝ) / 2 ^ 96) := by
      have e : fx (max (lo1 - hi0v) 0) * 2 ^ 16 * (((a - i * h : ℤ) : ℝ) / 2 ^ 96) =
          ((max (lo1 - hi0v) 0 * (a - i * h) : ℤ) : ℝ) / h / 2 ^ PR := by
        unfold fx PR; push_cast; rw [hh80]; field_simp; try ring
      have hr2 : fx (divD (max (lo1 - hi0v) 0 * (a - i * h)) h) ≤
          ((max (lo1 - hi0v) 0 * (a - i * h) : ℤ) : ℝ) / h / 2 ^ PR := by
        unfold fx; exact div_le_div_of_nonneg_right hround (by positivity)
      rw [fx_add', e]
      linarith
    linarith

end Prim

open Prim

/-- D6: the tabulated `arcsin` bounds are sound. -/
theorem asinTSound : AsinTSound := ⟨fun a ha => asinLoT_spec a ha, fun a => asinHiT_spec a⟩

end BHH.W3
