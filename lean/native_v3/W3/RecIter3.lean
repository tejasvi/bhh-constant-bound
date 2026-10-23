/-
Window-3 recursion: the iteration `W3C.recIter3` over the levels, with the mirror symmetry: only the
targets of the computed half (`halfCell`) are computed, the rows of the other half are the mirror copies
(`fullRows`), and `Φ` is the sum over the computed half of the closing sums (`sum_half`).
-/
import W3.RecLevel3

open Real

namespace BHH.W3.Rec

open W3C W2C BHH BHH.W2 BHH.Cert

attribute [local irreducible] W3C.NS W3C.reachable W3C.trs W3C.cls

/-- The results of the targets of the computed half. -/
def resI (lower : Bool) (rd : RecData3) (par : Bool) (n : ℕ) (rows : Array Row) : Array (Row × ℕ) :=
  pgen par (rd.NR * (rd.NT / 2)) (rd.NR * (rd.NT / 2)) fun h => targetRow lower rd rows (n == 0) (halfCell rd.NT h)

/-- The rows of the next level. -/
def rowsI (lower : Bool) (rd : RecData3) (par : Bool) (n : ℕ) (rows : Array Row) : Array Row :=
  fullRows rd.NR rd.NT (normRows lower ((resI lower rd par n rows).map (·.1))).1

/-- The scale of the next level. -/
def EI (lower : Bool) (rd : RecData3) (par : Bool) (n : ℕ) (rows : Array Row) (E : ℤ) : ℤ :=
  E - 14 + (PR : ℤ) - ((normRows lower ((resI lower rd par n rows).map (·.1))).2 : ℤ)

/-- The closing sum of the level. -/
def phiI (lower : Bool) (rd : RecData3) (par : Bool) (n : ℕ) (rows : Array Row) : ℕ :=
  (resI lower rd par n rows).foldl (fun acc rc => acc + rc.2) 0

/-- One iteration, unfolded (the pair `normRows` read by projections). -/
lemma recIter3_succ (lower : Bool) (rd : RecData3) (par : Bool) (n : ℕ) (rows : Array Row) (E : ℤ)
    (out : List (ℕ × ℤ)) :
    recIter3 lower rd par (n + 1) rows E out =
      recIter3 lower rd par n (rowsI lower rd par n rows) (EI lower rd par n rows E)
        (out ++ [(phiI lower rd par n rows, E - 14 + (PR : ℤ))]) := by
  rw [recIter3]; rfl

lemma recIter3_length (lower : Bool) (rd : RecData3) (par : Bool) :
    ∀ (fuel : ℕ) (rows : Array Row) (E : ℤ) (out : List (ℕ × ℤ)),
      (recIter3 lower rd par fuel rows E out).length = out.length + fuel := by
  intro fuel
  induction fuel with
  | zero => intro rows E out; rfl
  | succ k ih =>
    intro rows E out
    rw [recIter3_succ, ih]
    simp only [List.length_append, List.length_singleton]
    ring

lemma recIter3_prefix (lower : Bool) (rd : RecData3) (par : Bool) :
    ∀ (fuel : ℕ) (rows : Array Row) (E : ℤ) (out : List (ℕ × ℤ)),
      (recIter3 lower rd par fuel rows E out).take out.length = out := by
  intro fuel
  induction fuel with
  | zero => intro rows E out; simp [recIter3]
  | succ k ih =>
    intro rows E out
    rw [recIter3_succ]
    have h2 := ih (rowsI lower rd par k rows) (EI lower rd par k rows E)
      (out ++ [(phiI lower rd par k rows, E - 14 + (PR : ℤ))])
    simp only [List.length_append, List.length_singleton] at h2
    set L := recIter3 lower rd par k (rowsI lower rd par k rows) (EI lower rd par k rows E)
      (out ++ [(phiI lower rd par k rows, E - 14 + (PR : ℤ))])
    have : L.take out.length = (L.take (out.length + 1)).take out.length := by
      rw [List.take_take, min_eq_left (by omega)]
    rw [this, h2]
    simp

/-- The element `out.length` of an iteration with fuel `k + 1`: the closing sum of the first level. -/
lemma recIter3_first (lower : Bool) (rd : RecData3) (par : Bool) (k : ℕ) (rows : Array Row) (E : ℤ)
    (out : List (ℕ × ℤ)) :
    (recIter3 lower rd par (k + 1) rows E out)[out.length]! = (phiI lower rd par k rows, E - 14 + (PR : ℤ)) := by
  rw [recIter3_succ]
  have h2 := recIter3_prefix lower rd par k (rowsI lower rd par k rows) (EI lower rd par k rows E)
    (out ++ [(phiI lower rd par k rows, E - 14 + (PR : ℤ))])
  simp only [List.length_append, List.length_singleton] at h2
  set L := recIter3 lower rd par k (rowsI lower rd par k rows) (EI lower rd par k rows E)
    (out ++ [(phiI lower rd par k rows, E - 14 + (PR : ℤ))])
  have h3 : L[out.length]? = some (phiI lower rd par k rows, E - 14 + (PR : ℤ)) := by
    have := congrArg (fun l : List (ℕ × ℤ) => l[out.length]?) h2
    simp only [List.getElem?_take_of_lt (show out.length < out.length + 1 by omega)] at this
    rw [this]; simp
  rw [List.getElem!_eq_getElem?_getD, h3]; rfl

/-- The element `out.length + (m + 1)` of an iteration with fuel `k + 1`. -/
lemma recIter3_later (lower : Bool) (rd : RecData3) (par : Bool) (k m : ℕ) (rows : Array Row) (E : ℤ)
    (out : List (ℕ × ℤ)) :
    (recIter3 lower rd par (k + 1) rows E out)[out.length + (m + 1)]! =
      (recIter3 lower rd par k (rowsI lower rd par k rows) (EI lower rd par k rows E)
        (out ++ [(phiI lower rd par k rows, E - 14 + (PR : ℤ))]))[(out ++ [(phiI lower rd par k rows,
          E - 14 + (PR : ℤ))]).length + m]! := by
  rw [recIter3_succ]
  simp only [List.length_append, List.length_singleton]
  rw [show out.length + (m + 1) = out.length + 1 + m by ring]

/-! ## Half cells -/

lemma halfCell_lt {NR NT : ℕ} (hNT : 0 < NT) (hev : NT % 2 = 0) {h : ℕ} (hh : h < NR * (NT / 2)) :
    halfCell NT h < NR * NT := by
  unfold halfCell
  have hH : 0 < NT / 2 := by omega
  have h1 : h / (NT / 2) < NR := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hh)
  have h2 : h % (NT / 2) < NT / 2 := Nat.mod_lt _ hH
  have : h / (NT / 2) * NT + NT / 2 + h % (NT / 2) < (h / (NT / 2) + 1) * NT := by rw [add_mul, one_mul]; omega
  exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ h1)

lemma halfCell_up {NR NT c : ℕ} (hNT : 0 < NT) (hev : NT % 2 = 0) (hc : c < NR * NT) (hup : NT / 2 ≤ c % NT) :
    c / NT * (NT / 2) + (c % NT - NT / 2) < NR * (NT / 2) ∧
      halfCell NT (c / NT * (NT / 2) + (c % NT - NT / 2)) = c := by
  have hH : 0 < NT / 2 := by omega
  have h1 : c / NT < NR := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hc)
  have h2 : c % NT < NT := Nat.mod_lt _ hNT
  have hb : c % NT - NT / 2 < NT / 2 := by omega
  constructor
  · have : c / NT * (NT / 2) + (c % NT - NT / 2) < (c / NT + 1) * (NT / 2) := by rw [add_mul, one_mul]; omega
    exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ h1)
  · unfold halfCell
    rw [flat_div _ _ hb, flat_mod _ _ hb]
    conv_rhs => rw [← Nat.div_add_mod' c NT]
    omega

lemma halfCell_low {NR NT c : ℕ} (hNT : 0 < NT) (hev : NT % 2 = 0) (hc : c < NR * NT) (hlow : c % NT < NT / 2) :
    c / NT * (NT / 2) + (NT - 1 - c % NT - NT / 2) < NR * (NT / 2) ∧
      halfCell NT (c / NT * (NT / 2) + (NT - 1 - c % NT - NT / 2)) = mirC NT c := by
  have hH : 0 < NT / 2 := by omega
  have h1 : c / NT < NR := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hc)
  have h2 : c % NT < NT := Nat.mod_lt _ hNT
  have hb : NT - 1 - c % NT - NT / 2 < NT / 2 := by omega
  constructor
  · have : c / NT * (NT / 2) + (NT - 1 - c % NT - NT / 2) < (c / NT + 1) * (NT / 2) := by
      rw [add_mul, one_mul]; omega
    exact lt_of_lt_of_le this (Nat.mul_le_mul_right _ h1)
  · unfold halfCell mirC
    rw [flat_div _ _ hb, flat_mod _ _ hb]
    omega

/-! ## The bounds of the iteration -/

lemma pgen_half_ok (A : ℕ) : 0 < A ∨ A = 0 := by
  rcases Nat.eq_zero_or_pos A with h | h
  · right; exact h
  · left; exact h

lemma resI_size (lower : Bool) (rd : RecData3) (par : Bool) (n : ℕ) (rows : Array Row) :
    (resI lower rd par n rows).size = rd.NR * (rd.NT / 2) := by
  unfold resI; rw [pgen_size _ _ _ _ (pgen_half_ok _)]

lemma resI_get (lower : Bool) (rd : RecData3) (par : Bool) (n : ℕ) (rows : Array Row) {h : ℕ}
    (hh : h < rd.NR * (rd.NT / 2)) :
    (resI lower rd par n rows)[h]! = targetRow lower rd rows (n == 0) (halfCell rd.NT h) := by
  unfold resI; rw [pgen_get _ _ _ _ (pgen_half_ok _) hh]

lemma phiI_eq (lower : Bool) (rd : RecData3) (par : Bool) (n : ℕ) (rows : Array Row) :
    phiI lower rd par n rows =
      ∑ h ∈ Finset.range (rd.NR * (rd.NT / 2)), (targetRow lower rd rows (n == 0) (halfCell rd.NT h)).2 := by
  unfold phiI resI; rw [pgen_eq _ _ _ _ (pgen_half_ok _), foldl_snd_range]

section Iter

variable {lower : Bool} {rd : RecData3} {g : GridR} {D : DiscData3} {t : ℝ}

/-- The closing sum of a level bounds half the sum of all the exact closing sums. -/
theorem phiI_bd (hrd : RdOK lower rd g D t) (hm : MirOK g D) (hev : g.NT % 2 = 0) {rows : Array Row} {E : ℤ}
    {n : ℕ} (hrows : RowsBd lower g D t rows E n) (hmant : MantBd rows (g.NR * g.NT)) (par : Bool) (k : ℕ) :
    Bd lower ((phiI lower rd par k rows : ℝ) * (2 : ℝ) ^ (-(E - 14 + PR)))
      ((1 / 2) * ∑ cc ∈ Finset.range (g.NR * g.NT), Clo g D t n cc) := by
  rw [phiI_eq, sum_half hrd.NTpos hev _ (fun c hc => Clo_mirC hrd.NTpos hm t n hc),
    show ∀ X : ℝ, (1 : ℝ) / 2 * (2 * X) = X from fun X => by ring]
  push_cast
  rw [Finset.sum_mul, hrd.NR, hrd.NT]
  apply Bd.sum
  intro h hh
  rw [Finset.mem_range] at hh
  rw [← hrd.NT]
  exact (targetRow_bd hrd hrows hmant (by rw [hrd.NT]; exact halfCell_lt hrd.NTpos hev hh) _).1

/-- The rows of the next level (not after the last level). -/
theorem rowsI_bd (hrd : RdOK lower rd g D t) (hm : MirOK g D) (hev : g.NT % 2 = 0) {rows : Array Row} {E : ℤ}
    {n : ℕ} (hrows : RowsBd lower g D t rows E n) (hmant : MantBd rows (g.NR * g.NT)) (par : Bool) {k : ℕ}
    (hk : k ≠ 0) :
    RowsBd lower g D t (rowsI lower rd par k rows) (EI lower rd par k rows E) (n + 1) := by
  have hNT := hrd.NTpos
  have hk0 : (k == 0) = false := by simp [hk]
  intro c hc
  have hsz : ((resI lower rd par k rows).map (·.1)).size = g.NR * (g.NT / 2) := by
    rw [Array.size_map, resI_size, hrd.NR, hrd.NT]
  -- the rows of the half
  have hhalf : ∀ h < g.NR * (g.NT / 2),
      (normRows lower ((resI lower rd par k rows).map (·.1))).1[h]! =
        normRow lower (normRows lower ((resI lower rd par k rows).map (·.1))).2
          (targetRow lower rd rows false (halfCell g.NT h)).1 := by
    intro h hh
    rw [normRows_get _ _ (by rw [hsz]; exact hh), getElem!_map _ _ (by rw [resI_size, hrd.NR, hrd.NT]; exact hh),
      resI_get _ _ _ _ _ (by rw [hrd.NR, hrd.NT]; exact hh), hk0, hrd.NT]
  unfold rowsI EI
  rw [hrd.NR, hrd.NT, fullRows_get _ _ _ hc]
  set sh := (normRows lower ((resI lower rd par k rows).map (·.1))).2
  split_ifs with hup
  · obtain ⟨hlt, heq⟩ := halfCell_up hNT hev hc hup
    rw [hhalf _ hlt, heq]
    have hT := (targetRow_bd hrd hrows hmant hc false).2 rfl
    refine ⟨rowWF_normRow _ _ _ _ hT.1, rowInv_normRow _ _ _ hT.2.1, fun ca hca s hs => ?_⟩
    exact Bd.trans (normRow_bd lower sh _ (E - 14 + PR) ca s) (hT.2.2 ca hca s hs)
  · push_neg at hup
    obtain ⟨hlt, heq⟩ := halfCell_low hNT hev hc hup
    rw [hhalf _ hlt, heq]
    have hmc : mirC g.NT c < g.NR * g.NT := mirC_lt hNT hc
    have hT := (targetRow_bd hrd hrows hmant hmc false).2 rfl
    have hwf := rowWF_normRow lower sh _ _ hT.1
    refine ⟨rowWF_mir hNT _ hwf, rowInv_mir _ _ (rowInv_normRow _ _ _ hT.2.1), fun ca hca s hs => ?_⟩
    rw [rowVal_mir hNT _ hwf.ca hca]
    have h1 := Bd.trans (normRow_bd lower sh _ (E - 14 + PR) (mirC g.NT ca) s)
      (hT.2.2 (mirC g.NT ca) (mirC_lt hNT hca) s hs)
    rw [Fx_mirC hNT hm t (n + 1) c ca s hc hca] at h1
    exact h1

/-- The rows of the next level are normalised: mantissas at most `2^62`. -/
theorem rowsI_mant (hrd : RdOK lower rd g D t) (hev : g.NT % 2 = 0) (par : Bool) (k : ℕ) (rows : Array Row) :
    MantBd (rowsI lower rd par k rows) (g.NR * g.NT) := by
  have hNT := hrd.NTpos
  intro c hc q
  have hsz : ((resI lower rd par k rows).map (·.1)).size = g.NR * (g.NT / 2) := by
    rw [Array.size_map, resI_size, hrd.NR, hrd.NT]
  unfold rowsI
  rw [hrd.NR, hrd.NT, fullRows_get _ _ _ hc]
  split_ifs with hup
  · obtain ⟨hlt, _⟩ := halfCell_up hNT hev hc hup
    exact normRows_mant lower _ (by rw [hsz]; exact hlt) q
  · push_neg at hup
    obtain ⟨hlt, _⟩ := halfCell_low hNT hev hc hup
    exact normRows_mant lower _ (by rw [hsz]; exact hlt) q

/-- The iteration: every appended `(value, scale)` bounds half the sum of the exact closing sums of its level. -/
theorem recIter3_bd (hrd : RdOK lower rd g D t) (hm : MirOK g D) (hev : g.NT % 2 = 0) (par : Bool) :
    ∀ (fuel n : ℕ) (rows : Array Row) (E : ℤ) (out : List (ℕ × ℤ)), RowsBd lower g D t rows E n →
      MantBd rows (g.NR * g.NT) → ∀ m < fuel, Bd lower (((recIter3 lower rd par fuel rows E out)[out.length + m]!.1 : ℝ) *
        (2 : ℝ) ^ (-(recIter3 lower rd par fuel rows E out)[out.length + m]!.2))
        ((1 / 2) * ∑ cc ∈ Finset.range (g.NR * g.NT), Clo g D t (n + m) cc) := by
  intro fuel
  induction fuel with
  | zero => intro n rows E out _ _ m hm; omega
  | succ k ih =>
    intro n rows E out hrows hmant m hmk
    rcases m with _ | m
    · rw [add_zero, recIter3_first]
      exact phiI_bd hrd hm hev hrows hmant par k
    · rw [recIter3_later]
      have hk : k ≠ 0 := by omega
      have := ih (n + 1) (rowsI lower rd par k rows) (EI lower rd par k rows E)
        (out ++ [(phiI lower rd par k rows, E - 14 + (PR : ℤ))]) (rowsI_bd hrd hm hev hrows hmant par hk)
        (rowsI_mant hrd hev par k rows) m (by omega)
      rw [show n + 1 + m = n + (m + 1) by ring] at this
      exact this

end Iter

end BHH.W3.Rec
