/-
Window-3 entry primitives: `CosSinTSound`, the table-based `cos`/`sin` `W3C.cosSinT W3C.mkCsTab`.

For `|t| ≤ 7 · 2^PR` the table branch is taken: the nearest node `q 2^-8` (`q = ⌊(t + 2^87) / 2^88⌋`, `|q| ≤ 1792`) has
the table entry `cosSin (q 2^88)` (sound by `cosSin_sound`), the remainder angle `r = t - q 2^88` (`|r| ≤ 2^87`) gets
the 13-term Taylor enclosure with the remainder bound of `Complex.exp_bound` (as in `sinCosSmall_spec`), then the
angle-addition formulas and `clip1`.
Helper lemmas are in the namespace `BHH.W3.Prim`.
-/
import W3.Interfaces
import BHH.Ivl.Trig

open BHH.Cert Real

noncomputable section

namespace BHH.W3

open BHH

namespace Prim

/-! ## Taylor enclosure with `n` terms -/

/-- the widened Taylor enclosures of `cos s`, `sin s`, `s = t / 2^(PR + r)`, `|s| ≤ 1`, with `n` terms (the pattern of
`sinCosSmall`, for any `n > 0`), given the result `(c, sa, last)` of the term recursion -/
lemma taylor_widen (t : ℤ) (r n : ℕ) (hn : 0 < n) (ht : |(t : ℝ) / 2 ^ (PR + r)| ≤ 1) {c sa last : Iv}
    (hres : taylorGo t r n (n + 1) 0 (Iv.int 1) ⟨0, 0⟩ ⟨0, 0⟩ = (c, sa, last)) :
    ivMem (Real.cos ((t : ℝ) / 2 ^ (PR + r)))
        (Iv.widen c (divU (((Max.max (Int.natAbs last.lo) (Int.natAbs last.hi) : ℕ) : ℤ) * ((n : ℤ) + 1)) n + 1)) ∧
      ivMem (Real.sin ((t : ℝ) / 2 ^ (PR + r)))
        (Iv.widen sa (divU (((Max.max (Int.natAbs last.lo) (Int.natAbs last.hi) : ℕ) : ℤ) * ((n : ℤ) + 1)) n + 1)) := by
  have h0 : ivMem (((t : ℝ) / 2 ^ (PR + r)) ^ 0 / (Nat.factorial 0 : ℝ)) (Iv.int 1) := by
    simpa using Iv.mem_int 1
  have hc0 : ivMem (cosPart 0 ((t : ℝ) / 2 ^ (PR + r))) ⟨0, 0⟩ := by simp [cosPart, ivMem]
  have hs0 : ivMem (sinPart 0 ((t : ℝ) / 2 ^ (PR + r))) ⟨0, 0⟩ := by simp [sinPart, ivMem]
  obtain ⟨hc, hsn, hlast⟩ :=
    taylorGo_spec t r n (n + 1) 0 (Iv.int 1) ⟨0, 0⟩ ⟨0, 0⟩ (by omega) (by omega) h0 hc0 hs0
  rw [hres] at hc hsn hlast
  simp only at hc hsn hlast
  have hb := cos_sin_taylor ((t : ℝ) / 2 ^ (PR + r)) ht n hn
  generalize hsdef : (t : ℝ) / 2 ^ (PR + r) = s at hc hsn hlast hb ht ⊢
  have hS := SC_pos
  have hmag := mag_bound hlast
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hpow : |s ^ n / (n.factorial : ℝ)| = |s| ^ n / n.factorial := by
    rw [abs_div, abs_pow, abs_of_pos hfac]
  rw [hpow] at hmag
  generalize hmagdef : Max.max (Int.natAbs last.lo) (Int.natAbs last.hi) = mag at hmag ⊢
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hrem : |s| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) * SC
      ≤ ((divU ((mag : ℤ) * ((n : ℤ) + 1)) n + 1 : ℤ) : ℝ) := by
    have h2 := le_divU ((mag : ℤ) * ((n : ℤ) + 1)) n (by exact_mod_cast hn)
    have e : |s| ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) * SC
        = (|s| ^ n / n.factorial * SC) * ((n : ℝ) + 1) / n := by
      push_cast; field_simp
    rw [e]
    push_cast at h2 ⊢
    calc (|s| ^ n / n.factorial * SC) * ((n : ℝ) + 1) / n
        ≤ (mag : ℝ) * ((n : ℝ) + 1) / n := by gcongr
      _ ≤ _ := h2
      _ ≤ _ := by linarith
  exact ⟨mem_widen_of_approx hc.1 hc.2 hb.1 hrem, mem_widen_of_approx hsn.1 hsn.2 hb.2 hrem⟩

/-! ## The table -/

lemma csTab_map_get {β : Type*} [Inhabited β] (n : ℕ) (f : ℕ → β) {q : ℕ} (hq : q < n) :
    ((Array.range n).map f)[q]! = f q := by
  rw [getElem!_pos ((Array.range n).map f) q (by simpa using hq)]
  simp

lemma STEPC_eq : W3C.STEPC = 309485009821345068724781056 := by unfold W3C.STEPC PR W3C.CK; norm_num

/-- the table entry of the node `q` -/
lemma csTab_node {q : ℤ} (hq1 : -1792 ≤ q) (hq2 : q ≤ 1792) :
    W3C.mkCsTab[(q + Int.ofNat (8 * 2 ^ W3C.CK)).toNat]! = cosSin (q * 309485009821345068724781056) := by
  have hck : (8 * 2 ^ W3C.CK : ℕ) = 2048 := by unfold W3C.CK; norm_num
  have hpk : (2 : ℤ) ^ (PR - W3C.CK) = 309485009821345068724781056 := by unfold PR W3C.CK; norm_num
  have h2048 : Int.ofNat 2048 = 2048 := rfl
  rw [hck, h2048]
  unfold W3C.mkCsTab
  rw [csTab_map_get _ _ (by unfold W3C.CK; omega), hck, hpk, h2048]
  congr 1
  have h1 : Int.ofNat (q + 2048).toNat = q + 2048 := by
    rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg (by omega)]
  rw [h1]
  ring

/-! ## `cosSinT` -/

/-- `cosSinT tab` is sound for any table whose entries at the nodes `|q| ≤ 1792` are `cosSin (q 2^88)` (stated for a
general table so that no table entry is ever evaluated). -/
theorem cosSinT_sound_of (tab : Array (Iv × Iv))
    (htab : ∀ q : ℤ, -1792 ≤ q → q ≤ 1792 →
      tab[(q + Int.ofNat (8 * 2 ^ W3C.CK)).toNat]! = cosSin (q * 309485009821345068724781056)) :
    CosSinSound (W3C.cosSinT tab) := by
  intro t ht
  have hONE : ONE.toNat = 79228162514264337593543950336 := by simp [ONE]
  have hP : (2 : ℕ) ^ PR = 79228162514264337593543950336 := by norm_num [PR]
  have hcond : t.natAbs + 2 ^ PR ≤ 8 * ONE.toNat := by rw [hONE, hP]; rw [hONE] at ht; omega
  unfold W3C.cosSinT
  rw [ite_eq_left hcond]
  dsimp only
  rw [STEPC_eq]
  have ht' : -(7 * 79228162514264337593543950336 : ℤ) ≤ t ∧ t ≤ 7 * 79228162514264337593543950336 := by
    rw [hONE] at ht; omega
  -- the node `q` and the remainder `r`
  set q := (t + 309485009821345068724781056 / 2) / 309485009821345068724781056 with hqdef
  have hK : (0 : ℤ) < 309485009821345068724781056 := by norm_num
  have hq1 : q * 309485009821345068724781056 ≤ t + 309485009821345068724781056 / 2 :=
    Int.ediv_mul_le _ hK.ne'
  have hq2 : t + 309485009821345068724781056 / 2 < (q + 1) * 309485009821345068724781056 :=
    Int.lt_ediv_add_one_mul_self _ hK
  have hhalf : (309485009821345068724781056 : ℤ) / 2 = 154742504910672534362390528 := by norm_num
  rw [hhalf] at hq1 hq2
  have hqlo : -1792 ≤ q := by omega
  have hqhi : q ≤ 1792 := by omega
  have hr1 : -154742504910672534362390528 ≤ t - q * 309485009821345068724781056 := by linarith
  have hr2 : t - q * 309485009821345068724781056 ≤ 154742504910672534362390528 := by linarith
  rw [htab q hqlo hqhi]
  -- the table entry
  have hnat : (q * 309485009821345068724781056).natAbs ≤ 7 * ONE.toNat := by rw [hONE]; omega
  obtain ⟨hc0, hs0⟩ := cosSin_sound _ hnat
  -- the Taylor enclosure of the remainder angle
  have hsmall : |((t - q * 309485009821345068724781056 : ℤ) : ℝ) / 2 ^ (PR + 0)| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (PR + 0)), div_le_one (by positivity)]
    have hb : |((t - q * 309485009821345068724781056 : ℤ) : ℝ)| ≤ 154742504910672534362390528 := by
      rw [abs_le]; constructor
      · have : ((-154742504910672534362390528 : ℤ) : ℝ) ≤ ((t - q * 309485009821345068724781056 : ℤ) : ℝ) := by
          exact_mod_cast hr1
        push_cast at this ⊢; linarith
      · exact_mod_cast hr2
    have : (154742504910672534362390528 : ℝ) ≤ 2 ^ (PR + 0) := by unfold PR; norm_num
    linarith
  rcases hT : taylorGo (t - q * 309485009821345068724781056) 0 W3C.NT2 (W3C.NT2 + 1) 0 (Iv.int 1) ⟨0, 0⟩ ⟨0, 0⟩
    with ⟨c, sa, last⟩
  obtain ⟨hcr, hsr⟩ := taylor_widen _ 0 W3C.NT2 (by unfold W3C.NT2; norm_num) hsmall hT
  simp only
  -- the angle addition
  have hX : fx t = fx (q * 309485009821345068724781056) +
      ((t - q * 309485009821345068724781056 : ℤ) : ℝ) / 2 ^ (PR + 0) := by
    unfold fx; push_cast; ring
  refine ⟨clip1_cos ?_, clip1_sin ?_⟩
  · rw [hX, Real.cos_add]
    exact Iv.mem_sub (Iv.mem_mul hc0 hcr) (Iv.mem_mul hs0 hsr)
  · rw [hX, Real.sin_add]
    exact Iv.mem_add (Iv.mem_mul hs0 hcr) (Iv.mem_mul hc0 hsr)

end Prim

open Prim

/-- D5: the table-based `cos`/`sin` is sound (for `|t| ≤ 7 · 2^PR`, where the table branch is taken). -/
theorem cosSinTSound : CosSinTSound := cosSinT_sound_of W3C.mkCsTab fun _ hq1 hq2 => csTab_node hq1 hq2

end BHH.W3
