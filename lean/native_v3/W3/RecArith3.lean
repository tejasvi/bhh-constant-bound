/-
Window-3 recursion: the directed arithmetic of `W3C.runT3`, both directions at once.  `Bd lower a b` says
that the computed value `a` is a lower (`lower = true`) or upper (`lower = false`) bound of the exact value `b`.
Products `mul62` (`⌊x y / 2^62⌋`, `+ 1` upward), powers `powK`, the product bound `mulTop` of `W2C`, the rounding
`rnd`, the kernels `kern` (W2's `KernSound`), the exponential tables `mkExpTabs` / `e1Of`, and the parallel array
generator `pgen` (equal to the sequential one).
-/
import W3.RecMirror
import W2.KernSound

open Real

namespace BHH.W3.Rec

open W3C W2C BHH BHH.W2 BHH.Cert

/-! ## Directed bounds -/

/-- `a` bounds `b` from below (`lower`) or from above. -/
def Bd (lower : Bool) (a b : ℝ) : Prop := if lower then a ≤ b else b ≤ a

section BdLemmas

variable {l : Bool} {a b c d : ℝ}

lemma Bd_true : Bd true a b ↔ a ≤ b := by simp [Bd]
lemma Bd_false : Bd false a b ↔ b ≤ a := by simp [Bd]

lemma Bd.of_eq (h : a = b) : Bd l a b := by cases l <;> simp [Bd, h]

lemma Bd.refl (l : Bool) (a : ℝ) : Bd l a a := Bd.of_eq rfl

lemma Bd.trans (h1 : Bd l a b) (h2 : Bd l b c) : Bd l a c := by
  cases l <;> simp only [Bd, Bool.false_eq_true, ite_false, ite_true] at * <;> linarith

lemma Bd.add (h1 : Bd l a b) (h2 : Bd l c d) : Bd l (a + c) (b + d) := by
  cases l <;> simp only [Bd, Bool.false_eq_true, ite_false, ite_true] at * <;> linarith

lemma Bd.sum {ι : Type*} {s : Finset ι} {f g : ι → ℝ} (h : ∀ i ∈ s, Bd l (f i) (g i)) :
    Bd l (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  cases l
  · simp only [Bd, Bool.false_eq_true, ite_false] at *
    exact Finset.sum_le_sum h
  · simp only [Bd, ite_true] at *
    exact Finset.sum_le_sum h

lemma Bd.mul_left (hc : 0 ≤ c) (h : Bd l a b) : Bd l (c * a) (c * b) := by
  cases l <;> simp only [Bd, Bool.false_eq_true, ite_false, ite_true] at * <;>
    exact mul_le_mul_of_nonneg_left h hc

lemma Bd.mul_right (hc : 0 ≤ c) (h : Bd l a b) : Bd l (a * c) (b * c) := by
  cases l <;> simp only [Bd, Bool.false_eq_true, ite_false, ite_true] at * <;>
    exact mul_le_mul_of_nonneg_right h hc

lemma Bd.mul (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (h1 : Bd l a b) (h2 : Bd l c d) :
    Bd l (a * c) (b * d) := by
  cases l <;> simp only [Bd, Bool.false_eq_true, ite_false, ite_true] at *
  · exact mul_le_mul h1 h2 hd ha
  · exact mul_le_mul h1 h2 hc hb

lemma Bd.div_right (hc : 0 < c) (h : Bd l a b) : Bd l (a / c) (b / c) := by
  cases l <;> simp only [Bd, Bool.false_eq_true, ite_false, ite_true] at * <;>
    exact div_le_div_of_nonneg_right h hc.le

lemma Bd.pow (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Bd l a b) (n : ℕ) : Bd l (a ^ n) (b ^ n) := by
  cases l <;> simp only [Bd, Bool.false_eq_true, ite_false, ite_true] at *
  · exact pow_le_pow_left₀ hb h n
  · exact pow_le_pow_left₀ ha h n

lemma Bd.ite {p : Prop} [Decidable p] {a' b' : ℝ} (h1 : p → Bd l a b) (h2 : ¬p → Bd l a' b') :
    Bd l (if p then a else a') (if p then b else b') := by
  split_ifs with hp
  · exact h1 hp
  · exact h2 hp

end BdLemmas

/-! ## Products and powers at scale `2^-62` -/

lemma mul62_floor (x y : ℕ) :
    x / 2 ^ 31 * (y / 2 ^ 31) + (x / 2 ^ 31 * (y % 2 ^ 31) + x % 2 ^ 31 * (y / 2 ^ 31) +
      x % 2 ^ 31 * (y % 2 ^ 31) / 2 ^ 31) / 2 ^ 31 = x * y / 2 ^ 62 := by
  set x1 := x / 2 ^ 31
  set x0 := x % 2 ^ 31
  set y1 := y / 2 ^ 31
  set y0 := y % 2 ^ 31
  have hx : x = x1 * 2 ^ 31 + x0 := (Nat.div_add_mod' x _).symm
  have hy : y = y1 * 2 ^ 31 + y0 := (Nat.div_add_mod' y _).symm
  have e : x * y = (x0 * y0 + (x1 * y0 + x0 * y1) * 2 ^ 31) + x1 * y1 * 2 ^ 62 := by rw [hx, hy]; ring
  rw [e, Nat.add_mul_div_right _ _ (by positivity), show (2 : ℕ) ^ 62 = 2 ^ 31 * 2 ^ 31 by norm_num,
    ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (by positivity)]
  ring_nf

lemma mul62_eq (lower : Bool) (x y : ℕ) :
    mul62 lower x y = if lower then x * y / 2 ^ 62 else x * y / 2 ^ 62 + 1 := by
  unfold mul62
  have h1 : x >>> 31 = x / 2 ^ 31 := Nat.shiftRight_eq_div_pow _ _
  have h2 : y >>> 31 = y / 2 ^ 31 := Nat.shiftRight_eq_div_pow _ _
  have h3 : x &&& m31 = x % 2 ^ 31 := by rw [m31_eq, Nat.and_two_pow_sub_one_eq_mod]
  have h4 : y &&& m31 = y % 2 ^ 31 := by rw [m31_eq, Nat.and_two_pow_sub_one_eq_mod]
  simp only [h1, h2, h3, h4, Nat.shiftRight_eq_div_pow, mul62_floor]

/-- `mul62` bounds `x y / 2^62`. -/
lemma mul62_bd (lower : Bool) (x y : ℕ) : Bd lower (mul62 lower x y : ℝ) ((x : ℝ) * y / 2 ^ 62) := by
  rw [mul62_eq]
  have hP : (0 : ℝ) < 2 ^ 62 := by positivity
  cases lower
  · simp only [Bd, Bool.false_eq_true, ite_false]
    rw [div_le_iff₀ hP]
    have := Nat.lt_div_mul_add (a := x * y) (b := 2 ^ 62) (by positivity)
    push_cast
    have h : ((x * y : ℕ) : ℝ) < ((x * y / 2 ^ 62 * 2 ^ 62 + 2 ^ 62 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h
    nlinarith
  · simp only [Bd, ite_true]
    rw [le_div_iff₀ hP]
    have := Nat.div_mul_le_self (x * y) (2 ^ 62)
    have h : ((x * y / 2 ^ 62 * 2 ^ 62 : ℕ) : ℝ) ≤ ((x * y : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h ⊢
    linarith

lemma mul62_bd' {lower : Bool} {x y : ℕ} {X Y : ℝ} (hX : Bd lower ((x : ℝ) / 2 ^ 62) X)
    (hY : Bd lower ((y : ℝ) / 2 ^ 62) Y) (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) :
    Bd lower ((mul62 lower x y : ℝ) / 2 ^ 62) (X * Y) := by
  have h1 := Bd.div_right (by positivity : (0 : ℝ) < 2 ^ 62) (mul62_bd lower x y)
  refine Bd.trans h1 ?_
  have e : (x : ℝ) * y / 2 ^ 62 / 2 ^ 62 = ((x : ℝ) / 2 ^ 62) * ((y : ℝ) / 2 ^ 62) := by ring
  rw [e]
  exact Bd.mul (by positivity) hX0 (by positivity) hY0 hX hY

/-- `powK` bounds `2^62 (x / 2^62)^j`. -/
theorem powK_bd (lower : Bool) (x : ℕ) : ∀ j, Bd lower (powK lower x j : ℝ) (2 ^ 62 * ((x : ℝ) / 2 ^ 62) ^ j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | _ | j
    · rw [powK]; apply Bd.of_eq; norm_num [P62]
    · rw [powK]; apply Bd.of_eq; rw [zero_add, pow_one]; field_simp
    · rw [powK]
      set y : ℝ := (x : ℝ) / 2 ^ 62 with hy
      have hy0 : 0 ≤ y := by positivity
      have hP : (0 : ℝ) < 2 ^ 62 := by positivity
      have ihm := ih ((j + 1 + 1) / 2) (by omega)
      have hh2 : Bd lower (mul62 lower (powK lower x ((j + 1 + 1) / 2)) (powK lower x ((j + 1 + 1) / 2)) : ℝ)
          (2 ^ 62 * y ^ (2 * ((j + 1 + 1) / 2))) := by
        refine Bd.trans (mul62_bd lower _ _) ?_
        have e : 2 ^ 62 * y ^ (2 * ((j + 1 + 1) / 2)) =
            (2 ^ 62 * y ^ ((j + 1 + 1) / 2)) * (2 ^ 62 * y ^ ((j + 1 + 1) / 2)) / 2 ^ 62 := by
          rw [two_mul, pow_add]; ring
        rw [e]
        have hb0 : (0 : ℝ) ≤ 2 ^ 62 * y ^ ((j + 1 + 1) / 2) := mul_nonneg (by norm_num) (pow_nonneg hy0 _)
        exact Bd.div_right hP (Bd.mul (Nat.cast_nonneg _) hb0 (Nat.cast_nonneg _) hb0 ihm ihm)
      split_ifs with hev
      · simp only [beq_iff_eq] at hev
        have e : 2 ^ 62 * y ^ (j + 1 + 1) = 2 ^ 62 * y ^ (2 * ((j + 1 + 1) / 2)) := by
          rw [show 2 * ((j + 1 + 1) / 2) = j + 1 + 1 by omega]
        rw [e]; exact hh2
      · simp only [beq_iff_eq] at hev
        have hk : j + 1 + 1 = 2 * ((j + 1 + 1) / 2) + 1 := by omega
        have e : 2 ^ 62 * y ^ (j + 1 + 1) = (2 ^ 62 * y ^ (2 * ((j + 1 + 1) / 2))) * (x : ℝ) / 2 ^ 62 := by
          conv_lhs => rw [hk]
          rw [pow_succ, hy]; ring
        rw [e]
        refine Bd.trans (mul62_bd lower _ x) ?_
        exact Bd.div_right hP (Bd.mul_right (Nat.cast_nonneg _) hh2)

/-- The powers of a bounded kernel: `powK lower x j / 2^62` bounds `Y^j` if `x / 2^62` bounds `Y ≥ 0`. -/
lemma powK_bd' {lower : Bool} {x : ℕ} {Y : ℝ} (hx : Bd lower ((x : ℝ) / 2 ^ 62) Y) (hY : 0 ≤ Y) (j : ℕ) :
    Bd lower ((powK lower x j : ℝ) / 2 ^ 62) (Y ^ j) := by
  have h1 := Bd.div_right (by positivity : (0 : ℝ) < 2 ^ 62) (powK_bd lower x j)
  refine Bd.trans h1 ?_
  rw [mul_div_cancel_left₀ _ (by positivity : (2 : ℝ) ^ 62 ≠ 0)]
  exact Bd.pow (by positivity) hY hx j

/-! ## `mulTop`, `rnd` -/

/-- `mulTop` (31-bit halves) bounds `v k / 2^76`. -/
lemma mulTop_bd (lower : Bool) (v k : ℕ) :
    Bd lower (mulTop lower (v >>> 31) (v &&& m31) (k >>> 31) (k &&& m31) : ℝ) ((v : ℝ) * k / 2 ^ 76) := by
  have hv := split31 v
  have hk := split31 k
  cases lower
  · simp only [Bd, Bool.false_eq_true, ite_false]
    have := le_mulTop_upper (v >>> 31) (v &&& m31) (k >>> 31) (k &&& m31) (and_m31_lt v) (and_m31_lt k)
    rw [← hv, ← hk] at this
    push_cast at this; exact this
  · simp only [Bd, ite_true]
    have := mulTop_lower_le (v >>> 31) (v &&& m31) (k >>> 31) (k &&& m31)
    rw [← hv, ← hk] at this
    push_cast at this; exact this

lemma rnd_bd (lower : Bool) (v sh : ℕ) : Bd lower (rnd lower v sh : ℝ) ((v : ℝ) / 2 ^ sh) := by
  cases lower
  · simp only [Bd, Bool.false_eq_true, ite_false]; exact le_rnd_upper v sh
  · simp only [Bd, ite_true]; exact rnd_lower_le v sh

lemma rnd_zero (lower : Bool) (sh : ℕ) : rnd lower 0 sh = 0 := by
  unfold rnd
  cases lower
  · simp only [Bool.false_eq_true, ite_false, zero_add, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (by have := Nat.one_le_two_pow (n := sh); omega)
  · simp

lemma rnd_sh0 (lower : Bool) (v : ℕ) : rnd lower v 0 = v := by
  unfold rnd; cases lower <;> simp

/-! ## Kernels -/

lemma upq_eq (a : ℤ) (dtl : ℕ) : W3C.upq a dtl = ubInt a dtl := rfl

lemma upq_dvd (a : ℤ) (dtl : ℕ) : (2 : ℤ) ^ dtl ∣ W3C.upq a dtl := ubInt_dvd a dtl

lemma upq_nonneg {a : ℤ} (ha : 0 ≤ a) (dtl : ℕ) : 0 ≤ W3C.upq a dtl := ubInt_nonneg ha dtl

/-- The kernels `kern`: `kern lower j dtl a / 2^62` bounds `e^{-(j / 2^dtl) fx(a)}` (`a ≥ 0` a multiple of `2^dtl`). -/
lemma kern_bd (lower : Bool) (j dtl : ℕ) {a : ℤ} (hd : (2 : ℤ) ^ dtl ∣ a) (ha : 0 ≤ a) :
    Bd lower ((kern lower j dtl a : ℝ) / 2 ^ 62) (Real.exp (-((j : ℝ) / 2 ^ dtl * fx a))) := by
  have hP : (0 : ℝ) < 2 ^ 62 := by positivity
  cases lower
  · simp only [Bd, Bool.false_eq_true, ite_false]
    rw [le_div_iff₀ hP]
    have := kern_upper j dtl a hd ha
    linarith
  · simp only [Bd, ite_true]
    rw [div_le_iff₀ hP]
    have := kern_lower j dtl a hd
    linarith

/-! ## The parallel generator -/

lemma ceil_div_mul (n nch : ℕ) (h : 0 < nch) : n ≤ nch * ((n + nch - 1) / nch) := by
  have := Nat.lt_div_mul_add (a := n + nch - 1) (b := nch) h
  rw [mul_comm]
  omega

/-- `pgen` with tasks is the sequential map. -/
lemma pgen_eq {α : Type} [Inhabited α] (par : Bool) (nch n : ℕ) (f : ℕ → α) (h : 0 < nch ∨ n = 0) :
    pgen par nch n f = (Array.range n).map f := by
  unfold pgen
  split_ifs
  · rw [foldl_chunks n ((n + nch - 1) / nch) f nch]
    have hmin : Min.min n (nch * ((n + nch - 1) / nch)) = n := by
      rcases h with h | h
      · exact min_eq_left (ceil_div_mul n nch h)
      · subst h; simp
    rw [hmin]
  · rfl

lemma pgen_get {α : Type} [Inhabited α] (par : Bool) (nch n : ℕ) (f : ℕ → α) (h : 0 < nch ∨ n = 0) {i : ℕ}
    (hi : i < n) : (pgen par nch n f)[i]! = f i := by
  rw [pgen_eq par nch n f h, getElem!_map _ _ (by simpa using hi), range_getElem! hi]

lemma pgen_size {α : Type} [Inhabited α] (par : Bool) (nch n : ℕ) (f : ℕ → α) (h : 0 < nch ∨ n = 0) :
    (pgen par nch n f).size = n := by
  rw [pgen_eq par nch n f h]; simp

/-! ## The exponential tables and `e1` -/

lemma fx_two_pow (n q : ℕ) (hq : q ≤ PR) : fx ((n : ℤ) * 2 ^ q) = (n : ℝ) / 2 ^ (PR - q) := by
  unfold fx
  have e : (2 : ℝ) ^ PR = 2 ^ (PR - q) * 2 ^ q := by rw [← pow_add]; congr 1; omega
  push_cast
  rw [e]; field_simp

lemma e1_tab_bd (lower : Bool) (dtl : ℕ) (par : Bool) (hdtl : dtl ≤ 48) (q : ℕ) (hq : 48 ≤ q) (hqP : q ≤ PR)
    {n : ℕ} (hn : n < P17) :
    Bd lower (((pgen par 64 P17 fun n => kern lower 1 dtl (Int.ofNat (n * 2 ^ q)))[n]! : ℕ) / (2 : ℝ) ^ 62)
      (Real.exp (-((n : ℝ) * 2 ^ (q - 48) / 2 ^ 48 / 2 ^ dtl))) := by
  rw [pgen_get par 64 P17 _ (Or.inl (by norm_num)) hn]
  have e : (Int.ofNat (n * 2 ^ q) : ℤ) = (n : ℤ) * 2 ^ q := by rw [Int.ofNat_eq_natCast]; push_cast; ring
  have hd : (2 : ℤ) ^ dtl ∣ Int.ofNat (n * 2 ^ q) := by
    rw [e]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _
  have h := kern_bd lower 1 dtl hd (by rw [e]; positivity)
  convert h using 2
  rw [e, fx_two_pow n q hqP]
  have e2 : (2 : ℝ) ^ (PR - q) * 2 ^ (q - 48) = 2 ^ 48 := by
    rw [← pow_add]; unfold PR; congr 1; unfold PR at hqP; omega
  push_cast
  field_simp
  rw [← e2]
  ring

lemma digits51 {a : ℕ} (ha : a < 2 ^ 51) :
    a = (a >>> 34) * 2 ^ 34 + ((a >>> 17) &&& M17) * 2 ^ 17 + (a &&& M17) ∧ a >>> 34 < P17 ∧
      (a >>> 17) &&& M17 < P17 ∧ a &&& M17 < P17 := by
  have hM : M17 = 2 ^ 17 - 1 := rfl
  have hP : P17 = 2 ^ 17 := rfl
  rw [hM, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, hP]
  omega

/-- `e1 = e^{-2^-dtl ā3}` at scale `2^-62` (directed), `ā3 = (v / 2) 2^-48`. -/
theorem e1Of_bd (lower : Bool) (dtl : ℕ) (par : Bool) (hdtl : dtl ≤ 48) (v : ℕ) :
    Bd lower ((e1Of lower dtl (mkExpTabs lower dtl par) v : ℝ) / 2 ^ 62)
      (Real.exp (-(((v / 2 : ℕ) : ℝ) / 2 ^ 48 / 2 ^ dtl))) := by
  unfold e1Of
  simp only
  by_cases h51 : v / 2 < P51
  · rw [if_pos h51]
    have h51' : v / 2 < 2 ^ 51 := h51
    obtain ⟨hdec, h2, h1, h0⟩ := digits51 h51'
    have b2 := e1_tab_bd lower dtl par hdtl (PR - 14) (by unfold PR; norm_num) (by omega) h2
    have b1 := e1_tab_bd lower dtl par hdtl (PR - 31) (by unfold PR; norm_num) (by omega) h1
    have b0 := e1_tab_bd lower dtl par hdtl (PR - 48) (by unfold PR; norm_num) (by omega) h0
    have hm := mul62_bd' (mul62_bd' b2 b1 (Real.exp_pos _).le (Real.exp_pos _).le) b0
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Real.exp_pos _).le
    have e : Real.exp (-(((v / 2 : ℕ) : ℝ) / 2 ^ 48 / 2 ^ dtl)) =
        Real.exp (-((((v / 2) >>> 34 : ℕ) : ℝ) * 2 ^ (PR - 14 - 48) / 2 ^ 48 / 2 ^ dtl)) *
        Real.exp (-(((((v / 2) >>> 17) &&& M17 : ℕ) : ℝ) * 2 ^ (PR - 31 - 48) / 2 ^ 48 / 2 ^ dtl)) *
        Real.exp (-((((v / 2) &&& M17 : ℕ) : ℝ) * 2 ^ (PR - 48 - 48) / 2 ^ 48 / 2 ^ dtl)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      have hc : ((v / 2 : ℕ) : ℝ) = (((v / 2) >>> 34 : ℕ) : ℝ) * 2 ^ 34 +
          ((((v / 2) >>> 17) &&& M17 : ℕ) : ℝ) * 2 ^ 17 + (((v / 2) &&& M17 : ℕ) : ℝ) := by
        exact_mod_cast hdec
      rw [hc]
      have p1 : PR - 14 - 48 = 34 := by unfold PR; norm_num
      have p2 : PR - 31 - 48 = 17 := by unfold PR; norm_num
      have p3 : PR - 48 - 48 = 0 := by unfold PR; norm_num
      rw [p1, p2, p3]
      ring
    rw [e]
    exact hm
  · rw [if_neg h51]
    have e : a3v v = ((v / 2 : ℕ) : ℤ) * 2 ^ (PR - 48) := by
      unfold a3v Q48; rw [Int.ofNat_eq_natCast]; push_cast; ring
    have hd : (2 : ℤ) ^ dtl ∣ a3v v := by
      rw [e]
      exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by unfold PR; omega)) _
    have h := kern_bd lower 1 dtl hd (by rw [e]; positivity)
    convert h using 2
    rw [e, fx_two_pow _ _ (by unfold PR; omega)]
    have p : PR - (PR - 48) = 48 := by unfold PR; norm_num
    rw [p]
    push_cast
    ring

/-! ## The `UInt64` product of the hot loop -/

lemma toUInt64_toNat {n : ℕ} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  have e : n.toUInt64.toNat = n % 2 ^ 64 := by simp
  rw [e, Nat.mod_eq_of_lt h]

/-- `mulTopU` computes `mulTop` exactly for a mantissa `≤ 2^62` and kernel halves `< 2^32`, `< 2^31`. -/
theorem mulTopU_toNat (lower : Bool) (v k1 k0 : UInt64) (hv : v.toNat ≤ 2 ^ 62) (hk1 : k1.toNat < 2 ^ 32)
    (hk0 : k0.toNat < 2 ^ 31) :
    (mulTopU lower v k1 k0).toNat = mulTop lower (v.toNat >>> 31) (v.toNat &&& m31) k1.toNat k0.toNat := by
  have hm : m31 = 2 ^ 31 - 1 := rfl
  have hg1 : v.toNat >>> 31 ≤ 2 ^ 31 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_of_le_mul (by omega)
  have hg0 : v.toNat &&& m31 < 2 ^ 31 := by
    have : v.toNat &&& m31 ≤ m31 := Nat.and_le_right
    omega
  have e1 : (v >>> 31).toNat = v.toNat >>> 31 := by simp [UInt64.toNat_shiftRight]
  have e0 : (v &&& 0x7FFFFFFF).toNat = v.toNat &&& m31 := by rw [UInt64.toNat_and]; rfl
  have p1 : (v.toNat >>> 31) * k1.toNat < 2 ^ 63 := by
    calc (v.toNat >>> 31) * k1.toNat ≤ 2 ^ 31 * k1.toNat := Nat.mul_le_mul_right _ hg1
      _ < 2 ^ 31 * 2 ^ 32 := by apply Nat.mul_lt_mul_of_pos_left hk1; positivity
      _ = 2 ^ 63 := by rw [← Nat.pow_add]
  have p2 : (v.toNat >>> 31) * k0.toNat < 2 ^ 62 + 1 := by
    calc (v.toNat >>> 31) * k0.toNat ≤ 2 ^ 31 * k0.toNat := Nat.mul_le_mul_right _ hg1
      _ ≤ 2 ^ 31 * 2 ^ 31 := Nat.mul_le_mul_left _ hk0.le
      _ < 2 ^ 62 + 1 := by norm_num
  have p3 : (v.toNat &&& m31) * k1.toNat < 2 ^ 63 := by
    calc (v.toNat &&& m31) * k1.toNat < 2 ^ 31 * 2 ^ 32 := Nat.mul_lt_mul'' hg0 hk1
      _ = 2 ^ 63 := by rw [← Nat.pow_add]
  have m1 : ((v >>> 31) * k1).toNat = (v.toNat >>> 31) * k1.toNat := by
    rw [UInt64.toNat_mul, e1]; exact Nat.mod_eq_of_lt (by omega)
  have m2 : ((v >>> 31) * k0).toNat = (v.toNat >>> 31) * k0.toNat := by
    rw [UInt64.toNat_mul, e1]; exact Nat.mod_eq_of_lt (by omega)
  have m3 : ((v &&& 0x7FFFFFFF) * k1).toNat = (v.toNat &&& m31) * k1.toNat := by
    rw [UInt64.toNat_mul, e0]; exact Nat.mod_eq_of_lt (by omega)
  have ms : ((v >>> 31) * k0 + (v &&& 0x7FFFFFFF) * k1).toNat =
      (v.toNat >>> 31) * k0.toNat + (v.toNat &&& m31) * k1.toNat := by
    rw [UInt64.toNat_add, m2, m3]; exact Nat.mod_eq_of_lt (by omega)
  have s1 : (((v >>> 31) * k1) >>> 14).toNat = ((v.toNat >>> 31) * k1.toNat) >>> 14 := by
    rw [UInt64.toNat_shiftRight, m1]; rfl
  have s2 : (((v >>> 31) * k0 + (v &&& 0x7FFFFFFF) * k1) >>> 45).toNat =
      ((v.toNat >>> 31) * k0.toNat + (v.toNat &&& m31) * k1.toNat) >>> 45 := by
    rw [UInt64.toNat_shiftRight, ms]; rfl
  have b1 : ((v.toNat >>> 31) * k1.toNat) >>> 14 < 2 ^ 63 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) p1
  have b2 : ((v.toNat >>> 31) * k0.toNat + (v.toNat &&& m31) * k1.toNat) >>> 45 < 2 ^ 20 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_lt_of_lt_mul (by omega)
  have st : (((v >>> 31) * k1) >>> 14 + ((v >>> 31) * k0 + (v &&& 0x7FFFFFFF) * k1) >>> 45).toNat =
      ((v.toNat >>> 31) * k1.toNat) >>> 14 +
        ((v.toNat >>> 31) * k0.toNat + (v.toNat &&& m31) * k1.toNat) >>> 45 := by
    rw [UInt64.toNat_add, s1, s2]; exact Nat.mod_eq_of_lt (by omega)
  unfold mulTopU mulTop
  cases lower
  · simp only [Bool.false_eq_true, ite_false]
    rw [UInt64.toNat_add, st]
    exact Nat.mod_eq_of_lt (by simp; omega)
  · simp only [ite_true]
    exact st

end BHH.W3.Rec
