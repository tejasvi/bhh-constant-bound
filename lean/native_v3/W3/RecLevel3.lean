/-
Window-3 recursion: the bounds of one level (`W3C.targetRow`: closing sum and the new row) and of level 2
(`W3C.c1Loop`, `W3C.level2`: the rows of `Fx 0` and `Φ_3`).
-/
import W3.RecStep3

open Real

namespace BHH.W3.Rec

open W3C W2C BHH BHH.W2 BHH.Cert

attribute [local irreducible] W3C.NS W3C.reachable W3C.trs W3C.cls

section Level

variable {lower : Bool} {rd : RecData3} {g : GridR} {D : DiscData3} {t : ℝ}

lemma inp_false (a b : Bool) : inp a b false = 4 * b2n a + 2 * b2n b := by
  unfold inp; rw [show b2n false = 0 from rfl, Nat.add_zero]

lemma inp_true (a b : Bool) : inp a b true = 4 * b2n a + 2 * b2n b + 1 := by
  unfold inp; rfl

lemma idx0 (q x : ℕ) : q + x * b2n false = q := by rw [show b2n false = 0 from rfl, Nat.mul_zero, Nat.add_zero]
lemma idx1 (q x : ℕ) : q + x * b2n true = q + x := by rw [show b2n true = 1 from rfl, Nat.mul_one]

/-- The bounds of one level: the closing sum of the target `cc`, and its row. -/
theorem targetRow_bd (hrd : RdOK lower rd g D t) {rows : Array Row} {E : ℤ} {n : ℕ}
    (hrows : RowsBd lower g D t rows E n) (hmant : MantBd rows (g.NR * g.NT)) {cc : ℕ} (hcc : cc < g.NR * g.NT)
    (last : Bool) :
    Bd lower (((targetRow lower rd rows last cc).2 : ℝ) * (2 : ℝ) ^ (-(E - 14 + PR))) (Clo g D t n cc) ∧
    (last = false → RowWF (g.NR * g.NT) (targetRow lower rd rows last cc).1 ∧
      RowInv (targetRow lower rd rows last cc).1 ∧
      ∀ cb < g.NR * g.NT, ∀ s < NS,
        Bd lower ((rowVal (targetRow lower rd rows last cc).1 cb s : ℝ) * (2 : ℝ) ^ (-(E - 14 + PR)))
          (Fx g D t (n + 1) cc cb s)) := by
  have hNC : rd.NR * rd.NT = g.NR * g.NT := by rw [hrd.NR, hrd.NT]
  have hw : wC g D cc = (rd.w[cc / rd.NT]! : ℝ) / 2 ^ PR := (hrd.w cc hcc).symm
  have ePR : (2 : ℝ) ^ (-(E - 14 + PR)) = (2 : ℝ) ^ (-(E - 14)) / 2 ^ PR := by
    rw [show -(E - 14 + (PR : ℤ)) = -(E - 14) - (PR : ℤ) by ring, zpow_sub₀ two_ne_zero, zpow_natCast]
  -- the accumulators of one source row
  have hb0 : ∀ cb < g.NR * g.NT, ∀ q < NS,
      Bd lower (((accS lower rd rows cc cb)[q]! : ℝ) * (2 : ℝ) ^ (-(E - 14))) (accX g D t n cc cb q false) := by
    intro cb hcb q hq
    have := accS_bd hrd hrows hmant hcc hcb hq false
    rw [idx0] at this; exact this
  have hb1 : ∀ cb < g.NR * g.NT, ∀ q < NS,
      Bd lower (((accS lower rd rows cc cb)[q + NS]! : ℝ) * (2 : ℝ) ^ (-(E - 14))) (accX g D t n cc cb q true) := by
    intro cb hcb q hq
    have := accS_bd hrd hrows hmant hcc hcb hq true
    rw [idx1] at this; exact this
  have hns0 : ∀ cb < g.NR * g.NT, nsOf rd cb cc = inp (nC g D cc) (sC g D cb cc) false := by
    intro cb hcb; rw [nsOf_eq hrd hcb hcc, inp_false]
  have hns1 : ∀ cb < g.NR * g.NT, ∀ q, q * 8 + nsOf rd cb cc + 1 = q * 8 + inp (nC g D cc) (sC g D cb cc) true := by
    intro cb hcb q; rw [nsOf_eq hrd hcb hcc, inp_true, Nat.add_assoc]
  constructor
  · rw [targetRow_snd, hNC, Clo_regroup, hw, ePR]
    push_cast
    have e : (∑ cb ∈ Finset.range (g.NR * g.NT), ((accOf lower rd rows cc cb)[NS]! : ℝ)) * (rd.w[cc / rd.NT]! : ℝ) *
        ((2 : ℝ) ^ (-(E - 14)) / 2 ^ PR) = (rd.w[cc / rd.NT]! : ℝ) / 2 ^ PR *
          ∑ cb ∈ Finset.range (g.NR * g.NT), ((accOf lower rd rows cc cb)[NS]! : ℝ) * (2 : ℝ) ^ (-(E - 14)) := by
      rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro cb _; ring
    rw [e]
    apply Bd.mul_left (by positivity)
    apply Bd.sum
    intro cb hcb
    rw [Finset.mem_range] at hcb
    rw [(accOf_get lower rd rows cc cb ((hrows cb hcb).1.st)).2, hns0 cb hcb]
    push_cast
    rw [Finset.sum_mul]
    apply Bd.sum
    intro q hq
    rw [Finset.mem_range] at hq
    rw [show q * 8 + inp (nC g D cc) (sC g D cb cc) false + 1 = q * 8 + inp (nC g D cc) (sC g D cb cc) true by
      rw [← hns0 cb hcb]; exact hns1 cb hcb q, add_mul, mul_assoc, mul_assoc]
    exact Bd.add (Bd.mul_left (Nat.cast_nonneg _) (hb0 cb hcb q hq))
      (Bd.mul_left (Nat.cast_nonneg _) (hb1 cb hcb q hq))
  · intro hl
    subst hl
    obtain ⟨hinv, hwf, hval⟩ := targetRow_fst lower rd rows cc
    refine ⟨by rw [← hNC]; exact hwf, hinv, fun cb hcb s hs => ?_⟩
    rw [hval cb s, if_pos ⟨by rw [hNC]; exact hcb, hs⟩, Fx_succ_regroup, hw, ePR,
      (accOf_get lower rd rows cc cb ((hrows cb hcb).1.st)).1 s hs, hns0 cb hcb]
    push_cast
    have e : (∑ q ∈ Finset.range NS,
        ((if trs[q * 8 + inp (nC g D cc) (sC g D cb cc) false]! = s then ((accS lower rd rows cc cb)[q]! : ℝ) else 0) +
          (if trs[q * 8 + inp (nC g D cc) (sC g D cb cc) false + 1]! = s then
            ((accS lower rd rows cc cb)[q + NS]! : ℝ) else 0))) * (rd.w[cc / rd.NT]! : ℝ) *
        ((2 : ℝ) ^ (-(E - 14)) / 2 ^ PR) = (rd.w[cc / rd.NT]! : ℝ) / 2 ^ PR *
          ∑ q ∈ Finset.range NS,
            ((if trs[q * 8 + inp (nC g D cc) (sC g D cb cc) false]! = s then
                ((accS lower rd rows cc cb)[q]! : ℝ) * (2 : ℝ) ^ (-(E - 14)) else 0) +
             (if trs[q * 8 + inp (nC g D cc) (sC g D cb cc) false + 1]! = s then
                ((accS lower rd rows cc cb)[q + NS]! : ℝ) * (2 : ℝ) ^ (-(E - 14)) else 0)) := by
      rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _
      split_ifs <;> ring
    rw [e]
    apply Bd.mul_left (by positivity)
    apply Bd.sum
    intro q hq
    rw [Finset.mem_range] at hq
    rw [show q * 8 + inp (nC g D cc) (sC g D cb cc) false + 1 = q * 8 + inp (nC g D cc) (sC g D cb cc) true by
      rw [← hns0 cb hcb]; exact hns1 cb hcb q]
    apply Bd.add
    · exact Bd.ite (fun _ => hb0 cb hcb q hq) (fun _ => Bd.refl _ _)
    · exact Bd.ite (fun _ => hb1 cb hcb q hq) (fun _ => Bd.refl _ _)

/-! ## Level 2 -/

/-- The level-2 data: first-step kernels and pair kernels as directed bounds. -/
structure L2OK (lower : Bool) (rd : RecData3) (f1 k2 : Array ℕ) (g : GridR) (D : DiscData3) (t : ℝ) : Prop where
  f1 : ∀ c < g.NR * g.NT, Bd lower ((f1[c / rd.NT]! : ℝ) / 2 ^ 62) (uC g D t c)
  k2 : ∀ ca < g.NR * g.NT, ∀ cb < g.NR * g.NT, Bd lower ((k2[pbcOf rd ca cb]! : ℝ) / 2 ^ 62) (k2C g D t ca cb)

lemma c1Pi_eq (rd : RecData3) (c1 c2 : ℕ) : c1Pi rd (c2 / rd.NT) (c2 % rd.NT) c1 = pbcOf rd c1 c2 := rfl

lemma c1D_eq (hrd : RdOK lower rd g D t) {c1 : ℕ} (hc1 : c1 < g.NR * g.NT) : c1D rd c1 = d1C g D c1 := by
  unfold c1D d1C; rw [hrd.nb c1 hc1]

lemma c1Idx_eq (hrd : RdOK lower rd g D t) {c1 c2 : ℕ} (hc1 : c1 < g.NR * g.NT) (hc2 : c2 < g.NR * g.NT) :
    c1Idx rd (c2 / rd.NT) (c2 % rd.NT) rd.nb[c2 / rd.NT]! c1 = d1C g D c1 * 8 + inp (nC g D c2) (sC g D c1 c2) false := by
  unfold c1Idx
  rw [c1D_eq hrd hc1, c1Pi_eq, hrd.nb c2 hc2, hrd.sb c1 hc1 c2 hc2, inp_false, Nat.add_assoc]

lemma c1V_bd (hrd : RdOK lower rd g D t) {f1 k2 : Array ℕ} (hl2 : L2OK lower rd f1 k2 g D t) {c1 c2 : ℕ}
    (hc1 : c1 < g.NR * g.NT) (hc2 : c2 < g.NR * g.NT) :
    Bd lower ((c1V lower rd f1 k2 (c2 / rd.NT) (c2 % rd.NT) c1 : ℝ) / 2 ^ (PR + 62))
      (wC g D c1 * uC g D t c1 * k2C g D t c1 c2) := by
  unfold c1V
  rw [c1Pi_eq]
  have h1 := Bd.div_right (by positivity : (0 : ℝ) < 2 ^ (PR + 62))
    (mul62_bd lower (rd.w[c1 / rd.NT]! * f1[c1 / rd.NT]!) k2[pbcOf rd c1 c2]!)
  refine Bd.trans h1 ?_
  have e : ((rd.w[c1 / rd.NT]! * f1[c1 / rd.NT]! : ℕ) : ℝ) * (k2[pbcOf rd c1 c2]! : ℝ) / 2 ^ 62 / 2 ^ (PR + 62) =
      ((rd.w[c1 / rd.NT]! : ℝ) / 2 ^ PR) * ((f1[c1 / rd.NT]! : ℝ) / 2 ^ 62) * ((k2[pbcOf rd c1 c2]! : ℝ) / 2 ^ 62) := by
    push_cast; rw [pow_add]; field_simp
  rw [e, hrd.w c1 hc1]
  exact Bd.mul (by have := wC_nonneg hrd hc1; positivity) (mul_nonneg (wC_nonneg hrd hc1) (Real.exp_pos _).le)
    (by positivity) (Real.exp_pos _).le (Bd.mul_left (wC_nonneg hrd hc1) (hl2.f1 c1 hc1)) (hl2.k2 c1 hc1 c2 hc2)

/-- The level-2 row and closing sum of the target `c2`. -/
noncomputable def l2Row (lower : Bool) (rd : RecData3) (f1 k2 : Array ℕ) (c2 : ℕ) : Row × ℕ :=
  c1Loop lower rd f1 k2 (c2 / rd.NT) (c2 % rd.NT) rd.nb[c2 / rd.NT]! rd.w[c2 / rd.NT]! (rd.NR * rd.NT) 0 Row.empty 0

lemma foldl_snd_range {α : Type} (n : ℕ) (F : ℕ → α × ℕ) :
    ((Array.range n).map F).foldl (fun acc rc => acc + rc.2) 0 = ∑ i ∈ Finset.range n, (F i).2 := by
  rw [Array.foldl_map, ← Array.foldl_toList, Array.toList_range, foldl_add_range, zero_add]

lemma level2_fst (lower : Bool) (rd : RecData3) (f1 k2 : Array ℕ) (par : Bool) {c2 : ℕ} (hc2 : c2 < rd.NR * rd.NT) :
    (level2 lower rd f1 k2 par).1[c2]! = (l2Row lower rd f1 k2 c2).1 := by
  unfold level2
  simp only
  rw [getElem!_map _ _ (by rw [pgen_size _ _ _ _ (Or.inl (by norm_num))]; exact hc2),
    pgen_get _ _ _ _ (Or.inl (by norm_num)) hc2]
  unfold l2Row
  generalize c1Loop lower rd f1 k2 (c2 / rd.NT) (c2 % rd.NT) rd.nb[c2 / rd.NT]! rd.w[c2 / rd.NT]! (rd.NR * rd.NT) 0
    Row.empty 0 = p
  obtain ⟨r, cs⟩ := p
  rfl

lemma level2_size (lower : Bool) (rd : RecData3) (f1 k2 : Array ℕ) (par : Bool) :
    (level2 lower rd f1 k2 par).1.size = rd.NR * rd.NT := by
  unfold level2
  simp only
  rw [Array.size_map, pgen_size _ _ _ _ (Or.inl (by norm_num))]

lemma level2_snd (lower : Bool) (rd : RecData3) (f1 k2 : Array ℕ) (par : Bool) :
    (level2 lower rd f1 k2 par).2 =
      ∑ c2 ∈ Finset.range (rd.NR * rd.NT), (l2Row lower rd f1 k2 c2).2 * rd.w[c2 / rd.NT]! := by
  unfold level2
  simp only
  rw [pgen_eq _ _ _ _ (Or.inl (by norm_num)), foldl_snd_range]
  apply Finset.sum_congr rfl
  intro c2 _
  unfold l2Row
  generalize c1Loop lower rd f1 k2 (c2 / rd.NT) (c2 % rd.NT) rd.nb[c2 / rd.NT]! rd.w[c2 / rd.NT]! (rd.NR * rd.NT) 0
    Row.empty 0 = p
  obtain ⟨r, cs⟩ := p
  rfl

/-- The level-2 rows bound `Fx 0` at scale `2^-(2 PR + 62)`. -/
theorem level2_rows (hrd : RdOK lower rd g D t) {f1 k2 : Array ℕ} (hl2 : L2OK lower rd f1 k2 g D t) (par : Bool) :
    RowsBd lower g D t (level2 lower rd f1 k2 par).1 ((2 * PR + 62 : ℕ) : ℤ) 0 := by
  have hNC : rd.NR * rd.NT = g.NR * g.NT := by rw [hrd.NR, hrd.NT]
  intro c2 hc2
  rw [level2_fst lower rd f1 k2 par (by rw [hNC]; exact hc2)]
  have hspec := c1Loop_spec lower rd f1 k2 (c2 / rd.NT) (c2 % rd.NT) rd.nb[c2 / rd.NT]! rd.w[c2 / rd.NT]!
    (rd.NR * rd.NT) (rd.NR * rd.NT) 0 Row.empty 0 (by omega) rowInv_empty
  unfold l2Row
  refine ⟨by rw [← hNC]; exact hspec.2.2.1 _ (rowWF_empty _) le_rfl, hspec.2.1, fun ca hca s hs => ?_⟩
  rw [hspec.2.2.2 ca s, rowVal_empty, zero_add]
  rw [Finset.sum_eq_single ca]
  · simp only [Fx, true_and]
    rw [c1D_eq hrd hca, c1Idx_eq hrd hca hc2]
    by_cases hc : d1C g D ca < NS ∧ trs[d1C g D ca * 8 + inp (nC g D c2) (sC g D ca c2) false]! = s
    · rw [if_pos ⟨hc.1, hc.2, hs⟩, if_pos hc]
      have e2 : (2 : ℝ) ^ (-(((2 * PR + 62 : ℕ) : ℤ))) = 1 / 2 ^ PR * (1 / 2 ^ (PR + 62)) := by
        rw [zpow_neg, zpow_natCast, show 2 * PR + 62 = PR + (PR + 62) by ring, pow_add]; field_simp
      rw [e2]
      push_cast
      have e3 : (c1V lower rd f1 k2 (c2 / rd.NT) (c2 % rd.NT) ca : ℝ) * (rd.w[c2 / rd.NT]! : ℝ) *
          (1 / 2 ^ PR * (1 / 2 ^ (PR + 62))) = ((rd.w[c2 / rd.NT]! : ℝ) / 2 ^ PR) *
            ((c1V lower rd f1 k2 (c2 / rd.NT) (c2 % rd.NT) ca : ℝ) / 2 ^ (PR + 62)) := by ring
      rw [e3, hrd.w c2 hc2]
      exact Bd.mul_left (wC_nonneg hrd hc2) (c1V_bd hrd hl2 hca hc2)
    · rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩), if_neg hc]
      simp only [Nat.cast_zero, zero_mul]; exact Bd.refl _ _
  · intro b _ hb; rw [if_neg (fun h => hb h.1)]
  · intro h; exact absurd (Finset.mem_Ico.mpr ⟨Nat.zero_le _, by rw [hNC]; exact hca⟩) h

/-- `Φ_3`: the level-2 closing sum (scale `2^-(2 PR + 62 + 1)`). -/
theorem level2_phi (hrd : RdOK lower rd g D t) {f1 k2 : Array ℕ} (hl2 : L2OK lower rd f1 k2 g D t) (par : Bool) :
    Bd lower (((level2 lower rd f1 k2 par).2 : ℝ) * (2 : ℝ) ^ (-(((2 * PR + 62 + 1 : ℕ) : ℤ)))) (Phi3x g D t) := by
  have hNC : rd.NR * rd.NT = g.NR * g.NT := by rw [hrd.NR, hrd.NT]
  rw [level2_snd, hNC]
  unfold Phi3x
  have e2 : (2 : ℝ) ^ (-(((2 * PR + 62 + 1 : ℕ) : ℤ))) = 1 / 2 * (1 / 2 ^ PR * (1 / 2 ^ (PR + 62))) := by
    rw [zpow_neg, zpow_natCast, show 2 * PR + 62 + 1 = 1 + (PR + (PR + 62)) by ring, pow_add, pow_add]; field_simp
  rw [e2]
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Bd.sum
  intro c2 hc2
  rw [Finset.mem_range] at hc2
  have hspec := c1Loop_spec lower rd f1 k2 (c2 / rd.NT) (c2 % rd.NT) rd.nb[c2 / rd.NT]! rd.w[c2 / rd.NT]!
    (rd.NR * rd.NT) (rd.NR * rd.NT) 0 Row.empty 0 (by omega) rowInv_empty
  unfold l2Row
  rw [hspec.1, zero_add, hNC, ← Finset.range_eq_Ico]
  push_cast
  have e3 : (∑ c ∈ Finset.range (g.NR * g.NT), (if c1D rd c < NS then
        ((cls[c1Idx rd (c2 / rd.NT) (c2 % rd.NT) rd.nb[c2 / rd.NT]! c]! : ℕ) : ℝ) *
          (c1V lower rd f1 k2 (c2 / rd.NT) (c2 % rd.NT) c : ℝ) else 0)) * (rd.w[c2 / rd.NT]! : ℝ) *
      (1 / 2 * (1 / 2 ^ PR * (1 / 2 ^ (PR + 62)))) =
      1 / 2 * ∑ c ∈ Finset.range (g.NR * g.NT), (if c1D rd c < NS then
        ((cls[c1Idx rd (c2 / rd.NT) (c2 % rd.NT) rd.nb[c2 / rd.NT]! c]! : ℕ) : ℝ) *
          (((rd.w[c2 / rd.NT]! : ℝ) / 2 ^ PR) * ((c1V lower rd f1 k2 (c2 / rd.NT) (c2 % rd.NT) c : ℝ) / 2 ^ (PR + 62)))
        else 0) := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> ring
  rw [e3]
  apply Bd.mul_left (by norm_num)
  apply Bd.sum
  intro ca hca
  rw [Finset.mem_range] at hca
  rw [c1D_eq hrd hca, c1Idx_eq hrd hca hc2]
  apply Bd.ite
  · intro _
    apply Bd.mul_left (Nat.cast_nonneg _)
    rw [hrd.w c2 hc2]
    exact Bd.mul_left (wC_nonneg hrd hc2) (c1V_bd hrd hl2 hca hc2)
  · intro _; exact Bd.refl _ _

end Level

end BHH.W3.Rec
