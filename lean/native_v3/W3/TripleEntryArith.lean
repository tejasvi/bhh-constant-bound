/-
Window-3 entries: the integer and fixed-point arithmetic of the window-3 entries (`W3Cert/Tab3.lean`).

* the Newton candidate of the integer square root is the floor square root (`isqrtCand n = Nat.sqrt n` for
  `n < 2^200`), so `Iv.sqrt` has a positive lower end on arguments with lower end in `[1, 2^104)` (the first form of
  `lvPairT` relies on it: it has no explicit positivity test);
* `te_lvPairT_spec`: on success `lvPairT` returns `0` for `d⁻ ≥ 2` and otherwise at least `2 · pairRem` (W2's integrated
  remainder; the factor `2` covers `ν ≤ 2`), with the tabulated `arcsin` (`AsinTSound`);
* `momentsX` on explicit lists, and the table lookups `rings`, `geoAt`, `hsAt` of `mkTabData`.
-/
import W3.Interfaces
import W2.FixSound
import W2.EntryDefs

open Real

namespace BHH.W3

open BHH BHH.Cert BHH.W2

/-! ## Fixed-point helpers -/

lemma te_fx_add (a b : ℤ) : fx (a + b) = fx a + fx b := by unfold fx; push_cast; ring
lemma te_fx_sub (a b : ℤ) : fx (a - b) = fx a - fx b := by unfold fx; push_cast; ring
lemma te_fx_neg (a : ℤ) : fx (-a) = -fx a := by unfold fx; push_cast; ring
lemma te_fx_mul_two (a : ℤ) : fx (2 * a) = 2 * fx a := by unfold fx; push_cast; ring
lemma te_fx_natMul (n : ℕ) (a : ℤ) : fx ((n : ℤ) * a) = (n : ℝ) * fx a := by unfold fx; push_cast; ring
lemma te_fx_zero : fx 0 = 0 := by unfold fx; simp
lemma te_fx_one_pos : (0 : ℝ) < fx 1 := by unfold fx; positivity
lemma te_fx_ONE : fx ONE = 1 := by
  unfold fx; rw [show ((ONE : ℤ) : ℝ) = 2 ^ PR by norm_num [ONE, PR]]; field_simp
lemma te_fx_two_ONE : fx (2 * ONE) = 2 := by
  unfold fx; rw [show ((2 * ONE : ℤ) : ℝ) = 2 * 2 ^ PR by norm_num [ONE, PR]]; field_simp
lemma te_fx_mono {a b : ℤ} (h : a ≤ b) : fx a ≤ fx b := fx_le_iff.mpr h
lemma te_fx_lt {a b : ℤ} (h : a < b) : fx a < fx b := by
  unfold fx; exact div_lt_div_of_pos_right (by exact_mod_cast h) (by positivity)
lemma te_fx_max (a b : ℤ) : fx (Max.max a b) = Max.max (fx a) (fx b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (te_fx_mono h)]
  · rw [max_eq_left h, max_eq_left (te_fx_mono h)]
lemma te_fx_min (a b : ℤ) : fx (Min.min a b) = Min.min (fx a) (fx b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (te_fx_mono h)]
  · rw [min_eq_right h, min_eq_right (te_fx_mono h)]

/-- `shrU (a * b) PR + 1` bounds the product of two fixed-point numbers from above. -/
lemma te_fx_shrU_mul (a b : ℤ) : fx a * fx b ≤ fx (shrU (a * b) PR + 1) := by
  have h := le_shrU (a * b) PR
  rw [te_fx_add]
  have h1 : fx a * fx b = ((a * b : ℤ) : ℝ) / 2 ^ PR / 2 ^ PR := by unfold fx; push_cast; field_simp
  have h2 : ((a * b : ℤ) : ℝ) / 2 ^ PR / 2 ^ PR ≤ fx (shrU (a * b) PR) := by
    unfold fx; exact div_le_div_of_nonneg_right h (by positivity)
  linarith [te_fx_one_pos]

/-- `fx (shrU a 1) ≥ fx a / 2` -/
lemma te_fx_shrU1 (a : ℤ) : fx a / 2 ≤ fx (shrU a 1) := by
  have h := le_shrU a 1
  unfold fx
  rw [div_div, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right (by simpa using h) (by positivity)

/-- `fx (shrD a 1) ≤ fx a / 2` -/
lemma te_fx_shrD1 (a : ℤ) : fx (shrD a 1) ≤ fx a / 2 := by
  have h := shrD_le a 1
  unfold fx
  rw [div_div, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right (by simpa using h) (by positivity)

lemma te_shrD1_nonneg {a : ℤ} (h : 0 ≤ a) : 0 ≤ shrD a 1 := by
  unfold shrD; rw [Int.shiftRight_eq_div_pow]; positivity

/-! ## Integer square roots: the Newton candidate is the floor square root -/

/-- AM-GM in `ℕ`: one Newton step never goes below the floor square root. -/
lemma te_sqrt_le_newton (n x : ℕ) (hx : 0 < x) : Nat.sqrt n ≤ (x + n / x) / 2 := by
  have h1 := Nat.lt_mul_div_succ n hx
  have h2 := Nat.sqrt_le n
  by_contra hlt
  push_neg at hlt
  have h3 : x + n / x + 1 ≤ 2 * Nat.sqrt n := by omega
  have h4 : x * (n / x + 1) ≤ Nat.sqrt n * Nat.sqrt n := by
    have : (x : ℤ) * ((n / x : ℕ) + 1) ≤ (Nat.sqrt n : ℤ) * Nat.sqrt n := by
      have h3' : (x : ℤ) + (n / x : ℕ) + 1 ≤ 2 * (Nat.sqrt n : ℤ) := by exact_mod_cast h3
      nlinarith [sq_nonneg ((Nat.sqrt n : ℤ) - x), (Nat.cast_nonneg x : (0 : ℤ) ≤ x)]
    exact_mod_cast this
  omega

/-- Above the floor square root, one Newton step at least halves the excess. -/
lemma te_newton_step (n x : ℕ) (hx : Nat.sqrt n < x) :
    (x + n / x) / 2 < x ∧ (x + n / x) / 2 - Nat.sqrt n ≤ (x - Nat.sqrt n) / 2 := by
  have h1 := Nat.lt_succ_sqrt n
  have hq : n / x ≤ Nat.sqrt n := by
    have hx0 : 0 < x := by omega
    have : n / x < Nat.sqrt n + 1 := by
      rw [Nat.div_lt_iff_lt_mul hx0]
      have : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ (Nat.sqrt n + 1) * x :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [Nat.succ_eq_add_one] at h1
      nlinarith
    omega
  constructor <;> omega

lemma te_isqrtGo_eq (n : ℕ) (h1 : 1 ≤ Nat.sqrt n) :
    ∀ f x, Nat.sqrt n ≤ x → x - Nat.sqrt n < 2 ^ f → isqrtGo n (f + 1) x = Nat.sqrt n := by
  have hstop : ∀ f, isqrtGo n (f + 1) (Nat.sqrt n) = Nat.sqrt n := by
    intro f
    have hs := Nat.sqrt_le n
    have hd : Nat.sqrt n ≤ n / Nat.sqrt n := (Nat.le_div_iff_mul_le (by omega)).2 hs
    show (let y := (Nat.sqrt n + n / Nat.sqrt n) / 2
      if y < Nat.sqrt n then isqrtGo n f y else Nat.sqrt n) = Nat.sqrt n
    simp only
    rw [if_neg (by omega)]
  intro f
  induction f with
  | zero =>
    intro x hx1 hx2
    have : x = Nat.sqrt n := by simp at hx2; omega
    subst this
    exact hstop 0
  | succ f ih =>
    intro x hx1 hx2
    rcases Nat.eq_or_lt_of_le hx1 with h | h
    · rw [← h]; exact hstop (f + 1)
    · obtain ⟨hy1, hy2⟩ := te_newton_step n x h
      have hy0 := te_sqrt_le_newton n x (by omega)
      show (let y := (x + n / x) / 2
        if y < x then isqrtGo n (f + 1) y else x) = Nat.sqrt n
      simp only
      rw [if_pos hy1]
      apply ih _ hy0
      have : (x - Nat.sqrt n) / 2 < 2 ^ f := by
        rw [pow_succ] at hx2; omega
      omega

lemma te_isqrtCand_eq (n : ℕ) (hn : n < 2 ^ 200) : isqrtCand n = Nat.sqrt n := by
  unfold isqrtCand
  split_ifs with h
  · interval_cases n <;> rfl
  · push_neg at h
    have h1 : 1 ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
    have hL : Nat.log2 n < 200 := by
      rw [Nat.log2_lt (by omega)]; exact hn
    have hx0 : Nat.sqrt n ≤ 2 ^ (Nat.log2 n / 2 + 1) := by
      have h2 := (Nat.lt_log2_self (n := n))
      have h3 : 2 ^ (Nat.log2 n + 1) ≤ 2 ^ (Nat.log2 n / 2 + 1) * 2 ^ (Nat.log2 n / 2 + 1) := by
        rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      exact (Nat.sqrt_lt.2 (by omega)).le
    have hx1 : 2 ^ (Nat.log2 n / 2 + 1) - Nat.sqrt n < 2 ^ 199 := by
      have : 2 ^ (Nat.log2 n / 2 + 1) ≤ 2 ^ 100 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : (2 : ℕ) ^ 100 < 2 ^ 199 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      omega
    exact te_isqrtGo_eq n h1 199 _ hx0 hx1

lemma te_isqrtLo_eq (n : ℕ) (hn : n < 2 ^ 200) : isqrtLo n = Nat.sqrt n := by
  unfold isqrtLo
  simp only
  rw [te_isqrtCand_eq n hn, if_pos (Nat.sqrt_le n)]

/-- The lower end of `Iv.sqrt` is positive when the argument's lower end is in `[1, 2^104)`. -/
lemma te_sqrt_lo_pos (a : Iv) (h1 : 1 ≤ a.lo) (h2 : a.lo < 2 ^ 104) : 0 < (Iv.sqrt a).lo := by
  unfold Iv.sqrt
  simp only
  rw [if_neg (by omega)]
  have hO : (ONE : ℤ) = 2 ^ 96 := by norm_num [ONE]
  have hm1 : 1 ≤ (a.lo * ONE).toNat := by
    have : 1 ≤ a.lo * ONE := by rw [hO]; nlinarith
    omega
  have hm2 : (a.lo * ONE).toNat < 2 ^ 200 := by
    have : a.lo * ONE < 2 ^ 200 := by
      rw [hO]
      calc a.lo * 2 ^ 96 < 2 ^ 104 * 2 ^ 96 := by
            exact mul_lt_mul_of_pos_right h2 (by positivity)
        _ = 2 ^ 200 := by norm_num
    have h0 : 0 ≤ a.lo * ONE := by rw [hO]; positivity
    zify [h0]
    rw [Int.toNat_of_nonneg h0]; exact_mod_cast this
  rw [te_isqrtLo_eq _ hm2]
  have : 1 ≤ Nat.sqrt (a.lo * ONE).toNat := Nat.le_sqrt.2 (by omega)
  omega


/-! ## `lvPairT` -/

lemma te_sqr_pt_hi_nonneg (dx : ℤ) : 0 ≤ (Iv.sqr ⟨dx, dx⟩).hi := by
  have h := ivMem_hi_le (Iv.mem_sqr (Iv.mem_pt dx))
  exact fx_nonneg_iff.mp (le_trans (sq_nonneg _) h)

/-- `λ ≥ 1/√(4 - d⁺²)` in the first form of `lvPairT` (the square root has a positive lower end). -/
lemma te_lam_spec {dx : ℤ} (hf : W2C.useFirstOf dx) :
    1 / √(4 - fx dx ^ 2) ≤ fx (Iv.inv (Iv.sqrt (Iv.sub (Iv.int 4) (Iv.sqr ⟨dx, dx⟩)))).hi := by
  have h1 : ivMem (fx dx ^ 2) (Iv.sqr ⟨dx, dx⟩) := Iv.mem_sqr (Iv.mem_pt dx)
  have h2 : ivMem (4 - fx dx ^ 2) (Iv.sub (Iv.int 4) (Iv.sqr ⟨dx, dx⟩)) := by
    have := Iv.mem_sub (Iv.mem_int 4) h1; push_cast at this; exact this
  have hpos : 0 < (Iv.sqrt (Iv.sub (Iv.int 4) (Iv.sqr ⟨dx, dx⟩))).lo := by
    apply te_sqrt_lo_pos
    · show 1 ≤ 4 * ONE - (Iv.sqr ⟨dx, dx⟩).hi
      have := hf.2; omega
    · show 4 * ONE - (Iv.sqr ⟨dx, dx⟩).hi < 2 ^ 104
      have := te_sqr_pt_hi_nonneg dx
      have : (4 : ℤ) * ONE < 2 ^ 104 := by norm_num [ONE]
      omega
  exact ivMem_hi_le (Iv.mem_inv (Iv.mem_sqrt h2) hpos)

lemma te_useFirst_dhi {dx : ℤ} (h : W2C.useFirstOf dx) : fx dx < 2 := by
  have h1 : dx * 100 < 198 * ONE := h.1
  have h2 : (dx : ℝ) * 100 < 198 * 2 ^ PR := by
    have : ((dx * 100 : ℤ) : ℝ) < ((198 * ONE : ℤ) : ℝ) := by exact_mod_cast h1
    rw [show ((198 * ONE : ℤ) : ℝ) = 198 * 2 ^ PR by norm_num [ONE, PR]] at this
    push_cast at this; exact this
  unfold fx
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) PR]

/-- Soundness of the pair remainder `lvPairT` (with the tabulated `arcsin`): on success `d⁻ > 0`; the value is `0`
when `d⁻ ≥ 2`, and otherwise it bounds `2 pairRem` (the factor `2` covers `ν ≤ 2`). -/
theorem te_lvPairT_spec (hAS : AsinTSound) {dn dx s1 s2 r : ℤ}
    (h : W3C.lvPairT W3C.mkAsinTab dn dx s1 s2 = some r) :
    0 < dn ∧ (2 * ONE ≤ dn → r = 0) ∧
    (dn < 2 * ONE → ∀ S1r S2r : ℝ, 0 ≤ S1r → 0 ≤ S2r → S1r ≤ fx s1 → S2r ≤ fx s2 →
      2 * pairRem (fx dn) (fx dx) (decide (W2C.useFirstOf dx)) S1r S2r ≤ fx r) := by
  unfold W3C.lvPairT at h
  by_cases h2 : 2 * ONE ≤ dn
  · rw [if_pos h2] at h
    have hO : (0 : ℤ) < 2 * ONE := by norm_num [ONE]
    refine ⟨by omega, fun _ => (Option.some.inj h).symm, fun h' => absurd h2 (not_le.mpr h')⟩
  rw [if_neg h2] at h
  by_cases h0 : dn ≤ 0
  · rw [if_pos h0] at h; exact absurd h (by simp)
  rw [if_neg h0] at h
  have hdn : 0 < dn := by omega
  refine ⟨hdn, fun h' => absurd h' h2, ?_⟩
  intro _ S1r S2r hS1 hS2 hS1r hS2r
  simp only [Option.some.injEq] at h
  rw [← h]
  have hdnr : 0 < fx dn := fx_pos_iff.mpr hdn
  -- the tangential term
  have htang : min (S2r / fx dn) (π * S1r) ≤
      fx (Min.min ((Iv.div ⟨s2, s2⟩ ⟨dn, dn⟩).hi) (shrU (piHi * s1) PR + 1)) := by
    rw [te_fx_min]
    apply min_le_min
    · have := Iv.mem_div (Iv.mem_pt s2) (Iv.mem_pt dn) hdn
      exact (div_le_div_of_nonneg_right hS2r hdnr.le).trans (ivMem_hi_le this)
    · calc π * S1r ≤ fx piHi * fx s1 :=
            mul_le_mul le_piHi hS1r hS1 (le_trans Real.pi_pos.le le_piHi)
        _ ≤ fx (shrU (piHi * s1) PR + 1) := te_fx_shrU_mul _ _
  -- the radial term
  unfold pairRem
  by_cases hf : W2C.useFirstOf dx
  · have hf' : dx * 100 < 198 * ONE ∧ (Iv.sqr ⟨dx, dx⟩).hi < 4 * ONE := hf
    rw [if_pos (decide_eq_true hf), if_pos hf']
    have hl := te_lam_spec hf
    have hrad : S2r / √(4 - fx dx ^ 2) ≤
        fx (shrU ((Iv.inv (Iv.sqrt (Iv.sub (Iv.int 4) (Iv.sqr ⟨dx, dx⟩)))).hi * s2) PR + 1) :=
      calc S2r / √(4 - fx dx ^ 2) = (1 / √(4 - fx dx ^ 2)) * S2r := by ring
        _ ≤ fx (Iv.inv (Iv.sqrt (Iv.sub (Iv.int 4) (Iv.sqr ⟨dx, dx⟩)))).hi * fx s2 :=
            mul_le_mul hl hS2r hS2 (le_trans (by positivity) hl)
        _ ≤ _ := te_fx_shrU_mul _ _
    rw [te_fx_mul_two, te_fx_add]
    linarith
  · have hf' : ¬ (dx * 100 < 198 * ONE ∧ (Iv.sqr ⟨dx, dx⟩).hi < 4 * ONE) := hf
    rw [if_neg (by simpa using hf), if_neg hf']
    set u : ℤ := if dx < 2 * ONE then W3C.asinHiT W3C.mkAsinTab (shrU dx 1) else W2C.halfPiHi with hu
    set w : ℤ := W3C.asinLoT W3C.mkAsinTab (shrD dn 1) with hw
    have hU : Real.arcsin (min (fx dx) 2 / 2) ≤ fx u := by
      rw [hu]
      split_ifs with hd
      · have hlt : fx dx < 2 := by have := te_fx_lt hd; rwa [te_fx_two_ONE] at this
        rw [min_eq_left hlt.le]
        exact (Real.arcsin_le_arcsin (te_fx_shrU1 dx)).trans (hAS.2 _)
      · exact (Real.arcsin_le_pi_div_two _).trans le_halfPiHi
    have hW : fx w ≤ Real.arcsin (fx dn / 2) := by
      rw [hw]
      exact (hAS.1 _ (te_shrD1_nonneg hdn.le)).trans (Real.arcsin_le_arcsin (te_fx_shrD1 dn))
    have hmu : 2 * Real.arcsin (min (fx dx) 2 / 2) - 2 * Real.arcsin (fx dn / 2) ≤
        fx (Max.max (2 * (u - w)) 0) := by
      rw [te_fx_max, te_fx_mul_two, te_fx_sub]
      exact le_trans (by linarith) (le_max_left _ _)
    have hmu0 : 0 ≤ fx (Max.max (2 * (u - w)) 0) := by
      rw [te_fx_max, te_fx_zero]; exact le_max_right _ _
    have hrad : (2 * Real.arcsin (min (fx dx) 2 / 2) - 2 * Real.arcsin (fx dn / 2)) * S1r ≤
        fx (shrU (Max.max (2 * (u - w)) 0 * s1) PR + 1) :=
      calc (2 * Real.arcsin (min (fx dx) 2 / 2) - 2 * Real.arcsin (fx dn / 2)) * S1r
          ≤ fx (Max.max (2 * (u - w)) 0) * S1r := mul_le_mul_of_nonneg_right hmu hS1
        _ ≤ fx (Max.max (2 * (u - w)) 0) * fx s1 := mul_le_mul_of_nonneg_left hS1r hmu0
        _ ≤ _ := te_fx_shrU_mul _ _
    rw [te_fx_mul_two, te_fx_add]
    linarith

section Tables

open W2C

lemma te_momentsX3 (a b c : ℕ) (x y z e : ℤ) : W3C.momentsX [a, b, c] [x, y, z] e =
    (e + a * x + b * y + c * z,
      shrU ((e + a * x + b * y + c * z) * (e + a * x + b * y + c * z)) PR + 1) := rfl

lemma te_momentsX2 (a b : ℕ) (x y e : ℤ) : W3C.momentsX [a, b] [x, y] e =
    (e + a * x + b * y, shrU ((e + a * x + b * y) * (e + a * x + b * y)) PR + 1) := rfl

lemma te_rings (g : Grid) {ir : ℕ} (hir : ir < g.NR) : (W3C.mkTabData g).rings[ir]! = mkRing g ir := by
  show ((Array.range g.NR).map (mkRing g))[ir]! = _
  rw [getElem!_map _ _ (by simpa using hir), range_getElem! hir]

lemma te_div_mod (W ir k : ℕ) (hk : k < W) : (ir * W + k) / W = ir ∧ (ir * W + k) % W = k := by
  have hW : 0 < W := by omega
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div hW, Nat.div_eq_of_lt hk, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]

lemma te_geoAt (g : Grid) {ir : ℕ} (hir : ir < g.NR) {j : ℤ} (hj : |j| ≤ 2 * g.NT) :
    W3C.geoAt g (W3C.mkTabData g).geo ir j = W3C.mkGeo g (mkRing g ir) (mkAData g).ch j := by
  have hj1 : 0 ≤ j + (2 * g.NT : ℕ) := by rw [abs_le] at hj; push_cast; omega
  have hj2 : (j + (2 * g.NT : ℕ)).toNat < 4 * g.NT + 1 := by rw [abs_le] at hj; push_cast; omega
  obtain ⟨hd, hm⟩ := te_div_mod (4 * g.NT + 1) ir _ hj2
  have hq : ir * (4 * g.NT + 1) + (j + (2 * g.NT : ℕ)).toNat < g.NR * (4 * g.NT + 1) := by
    have : (ir + 1) * (4 * g.NT + 1) ≤ g.NR * (4 * g.NT + 1) := Nat.mul_le_mul_right _ hir
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  show ((Array.range (g.NR * (4 * g.NT + 1))).map fun q =>
      W3C.mkGeo g ((Array.range g.NR).map (mkRing g))[q / (4 * g.NT + 1)]! (mkAData g).ch
        (((q % (4 * g.NT + 1) : ℕ) : ℤ) - ((2 * g.NT : ℕ) : ℤ)))[ir * (4 * g.NT + 1) +
          (j + ((2 * g.NT : ℕ) : ℤ)).toNat]! = _
  rw [getElem!_map _ _ (by simpa using hq), range_getElem! hq]
  rw [hd, hm, getElem!_map _ _ (by simpa using hir), range_getElem! hir]
  congr 1
  rw [Int.toNat_of_nonneg hj1]; ring

lemma te_hsAt (g : Grid) {ir ir2 : ℕ} (hir : ir < g.NR) (hir2 : ir2 < g.NR) {d : ℤ} (hd : |d| < g.NT) (e : ℤ) :
    W3C.hsAt (W3C.mkTabData g) ir ir2 d e =
      ((W3C.hullSum0 g (mkRing g ir) (mkRing g ir2) (mkAData g).ch d).1 - e,
        (W3C.hullSum0 g (mkRing g ir) (mkRing g ir2) (mkAData g).ch d).2 + e) := by
  have hNT : 1 ≤ g.NT := by
    have : (0 : ℤ) ≤ |d| := abs_nonneg d
    omega
  have hND : g.ND = 2 * g.NT - 1 := rfl
  have hk1 : 0 ≤ d + ((g.NT - 1 : ℕ) : ℤ) := by rw [abs_lt] at hd; push_cast [hNT]; omega
  have hk2 : (d + ((g.NT - 1 : ℕ) : ℤ)).toNat < g.ND := by rw [abs_lt] at hd; rw [hND]; push_cast [hNT]; omega
  set k := (d + ((g.NT - 1 : ℕ) : ℤ)).toNat with hk
  obtain ⟨hd1, hm1⟩ := te_div_mod g.ND (ir * g.NR + ir2) k hk2
  obtain ⟨hd2, hm2⟩ := te_div_mod g.NR ir ir2 hir2
  have hq : (ir * g.NR + ir2) * g.ND + k < g.NR * g.NR * g.ND := by
    have h1 : ir * g.NR + ir2 + 1 ≤ g.NR * g.NR := by
      have : (ir + 1) * g.NR ≤ g.NR * g.NR := Nat.mul_le_mul_right _ hir
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    have : (ir * g.NR + ir2 + 1) * g.ND ≤ g.NR * g.NR * g.ND := Nat.mul_le_mul_right _ h1
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have hq1 : ((ir * g.NR + ir2) * g.ND + k) / (g.NR * g.ND) = ir := by
    rw [Nat.mul_comm g.NR g.ND, ← Nat.div_div_eq_div_mul, hd1, hd2]
  have hq2 : (((ir * g.NR + ir2) * g.ND + k) / g.ND) % g.NR = ir2 := by rw [hd1, hm2]
  show (let r := ((Array.range (g.NR * g.NR * g.ND)).map fun q =>
      W3C.hullSum0 g ((Array.range g.NR).map (mkRing g))[q / (g.NR * g.ND)]!
        ((Array.range g.NR).map (mkRing g))[(q / g.ND) % g.NR]! (mkAData g).ch
        (((q % g.ND : ℕ) : ℤ) - ((g.NT - 1 : ℕ) : ℤ)))[(ir * g.NR + ir2) * g.ND +
          (d + ((g.NT - 1 : ℕ) : ℤ)).toNat]!
    (r.1 - e, r.2 + e)) = _
  rw [← hk, getElem!_map _ _ (by simpa using hq), range_getElem! hq]
  simp only
  rw [hq1, hq2, hm1, getElem!_map _ _ (by simpa using hir), range_getElem! hir,
    getElem!_map _ _ (by simpa using hir2), range_getElem! hir2]
  have : (k : ℤ) - ((g.NT - 1 : ℕ) : ℤ) = d := by rw [hk, Int.toNat_of_nonneg hk1]; ring
  rw [this]

end Tables

end BHH.W3
