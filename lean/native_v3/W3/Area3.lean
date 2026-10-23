/-
Shared part of the Laplace and discretisation bounds: measurability and bounds of `A_3` and of the
window-3 exponent `X_3` (`Xsum3`), and the window-3 area bound `A(y(z)) ≤ π + X_3(z)`:
`A(y) = π + Σ_{i ≥ 1} |B_i \ (B_0 ∪ ... ∪ B_{i-1})| ≤ π + A_1(z_0) + A_2(z_0, z_1) + Σ_{i ≥ 3} |B_i \ (B_{i-1} ∪ B_{i-2} ∪ B_{i-3})|`,
each difference translated by `y_{i-1}`.  The pattern of W2's `LapArea.lean`.
-/
import W3.Defs
import W2.LapArea
import W2.Disc

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W3.Lap

open BHH BHH.W2 BHH.W3

variable {m : ℕ}

/-! ## `A_3`: measurability and bounds -/

lemma measurable_A3 : Measurable fun q : Pt × (Pt × Pt) => A3 q.1 q.2.1 q.2.2 := by
  have hE : MeasurableSet {r : (Pt × (Pt × Pt)) × Pt |
      r.2 ∈ disk r.1.2.2 1 \ (disk 0 1 ∪ disk (-r.1.2.1) 1 ∪ disk (-r.1.2.1 - r.1.1) 1)} := by
    have h1 : MeasurableSet {r : (Pt × (Pt × Pt)) × Pt | sqDist r.2 r.1.2.2 ≤ 1 ^ 2} :=
      measurableSet_le (by unfold sqDist; fun_prop) measurable_const
    have h2 : MeasurableSet {r : (Pt × (Pt × Pt)) × Pt | sqDist r.2 0 ≤ 1 ^ 2} :=
      measurableSet_le (by unfold sqDist; fun_prop) measurable_const
    have h3 : MeasurableSet {r : (Pt × (Pt × Pt)) × Pt | sqDist r.2 (-r.1.2.1) ≤ 1 ^ 2} :=
      measurableSet_le (by unfold sqDist; fun_prop) measurable_const
    have h4 : MeasurableSet {r : (Pt × (Pt × Pt)) × Pt | sqDist r.2 (-r.1.2.1 - r.1.1) ≤ 1 ^ 2} :=
      measurableSet_le (by unfold sqDist; fun_prop) measurable_const
    exact h1.inter ((h2.union h3).union h4).compl
  have := measurable_measure_prodMk_left (ν := (volume : Measure Pt)) hE
  exact this.ennreal_toReal

lemma A3_nonneg (w' w z : Pt) : 0 ≤ A3 w' w z := ENNReal.toReal_nonneg

lemma A3_le_pi (w' w z : Pt) : A3 w' w z ≤ π := by
  unfold A3
  have h : volume (disk z 1 \ (disk 0 1 ∪ disk (-w) 1 ∪ disk (-w - w') 1)) ≤ ENNReal.ofReal π :=
    (volume_disk_one z) ▸ measure_mono sdiff_subset
  rw [← ENNReal.toReal_ofReal Real.pi_pos.le]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h

/-! ## `X_3`: measurability and bounds -/

/-- the `j`-th term (`j ≥ 1`) of `X_3`: `A_2(z_0, z_1)` for `j = 1`, `A_3(z_{j-2}, z_{j-1}, z_j)` for `j ≥ 2` -/
def x3 (z : Fin m → Pt) (j : ℕ) : ℝ :=
  if j = 1 then A2 (zget z 0) (zget z 1) else A3 (zget z (j - 2)) (zget z (j - 1)) (zget z j)

lemma Xsum3_eq (z : Fin m → Pt) : Xsum3 z = A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 m, x3 z j := rfl

lemma x3_nonneg (z : Fin m → Pt) (j : ℕ) : 0 ≤ x3 z j := by
  unfold x3; split_ifs
  · exact A2_nonneg _ _
  · exact A3_nonneg _ _ _

lemma x3_le_pi (z : Fin m → Pt) (j : ℕ) : x3 z j ≤ π := by
  unfold x3; split_ifs
  · exact A2_le_pi _ _
  · exact A3_le_pi _ _ _

lemma measurable_x3 (j : ℕ) : Measurable fun z : Fin m → Pt => x3 z j := by
  unfold x3
  by_cases hj : j = 1
  · simp only [hj, ↓reduceIte]
    simpa only [Function.comp_def] using
      measurable_A2.comp ((measurable_zget (m := m) 0).prodMk (measurable_zget 1))
  · simp only [hj, ↓reduceIte]
    simpa only [Function.comp_def] using
      measurable_A3.comp ((measurable_zget (m := m) (j - 2)).prodMk
        ((measurable_zget (m := m) (j - 1)).prodMk (measurable_zget j)))

lemma measurable_Xsum3 : Measurable (Xsum3 (m := m)) := by
  have e : Xsum3 (m := m) = fun z => A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 m, x3 z j := rfl
  rw [e]
  exact (measurable_A1.comp (measurable_zget 0)).add (Finset.measurable_sum _ fun j _ => measurable_x3 j)

lemma Xsum3_nonneg (z : Fin m → Pt) : 0 ≤ Xsum3 z :=
  add_nonneg (A1_nonneg _) (Finset.sum_nonneg fun j _ => x3_nonneg z j)

lemma Xsum3_le (z : Fin m → Pt) : Xsum3 z ≤ π + m * π := by
  rw [Xsum3_eq]
  have h1 := A1_le_pi (zget z 0)
  have h2 : ∑ j ∈ Finset.Ico 1 m, x3 z j ≤ ∑ _j ∈ Finset.Ico 1 m, π := Finset.sum_le_sum fun j _ => x3_le_pi z j
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h2
  have : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
  nlinarith [Real.pi_pos]

/-! ## The window-3 area bound -/

/-- translation invariance of the areas of differences of disks (three disks removed) -/
lemma volume_disk_diff3_translate (a b c d v : Pt) :
    volume (disk (a + v) 1 \ (disk (b + v) 1 ∪ disk (c + v) 1 ∪ disk (d + v) 1)) =
      volume (disk a 1 \ (disk b 1 ∪ disk c 1 ∪ disk d 1)) := by
  have e : disk (a + v) 1 \ (disk (b + v) 1 ∪ disk (c + v) 1 ∪ disk (d + v) 1) =
      (fun p => p + (-v)) ⁻¹' (disk a 1 \ (disk b 1 ∪ disk c 1 ∪ disk d 1)) := by
    ext p
    simp only [disk, sqDist, mem_sdiff, mem_union, mem_ofPred_eq, mem_preimage, Prod.fst_add, Prod.snd_add,
      Prod.fst_neg, Prod.snd_neg]
    ring_nf
  rw [e, measure_preimage_add_right]

lemma yN_add_two (z : Fin m → Pt) (n : ℕ) : yN z (n + 2) = yN z n + zget z n + zget z (n + 1) := by
  rw [show n + 2 = n + 1 + 1 from rfl, yN_succ, yN_succ]

lemma yN_add_three (z : Fin m → Pt) (n : ℕ) :
    yN z (n + 3) = yN z n + zget z n + zget z (n + 1) + zget z (n + 2) := by
  rw [show n + 3 = n + 2 + 1 from rfl, yN_succ, yN_add_two]

/-- the area of the new part of the disk at `y_{n+3}` beyond the disks at `y_{n+2}, y_{n+1}, y_n` is
`A_3(z_n, z_{n+1}, z_{n+2})` -/
lemma volume_new3 (z : Fin m → Pt) (n : ℕ) :
    volume (disk (yN z (n + 3)) 1 \ (disk (yN z (n + 2)) 1 ∪ disk (yN z (n + 1)) 1 ∪ disk (yN z n) 1)) =
      ENNReal.ofReal (A3 (zget z n) (zget z (n + 1)) (zget z (n + 2))) := by
  have h1 : yN z (n + 3) = zget z (n + 2) + yN z (n + 2) := by
    rw [yN_add_three, yN_add_two]; abel
  have h3 : yN z (n + 1) = -zget z (n + 1) + yN z (n + 2) := by
    rw [yN_add_two, yN_succ]; abel
  have h4 : yN z n = (-zget z (n + 1) - zget z n) + yN z (n + 2) := by
    rw [yN_add_two]; abel
  have ht := volume_disk_diff3_translate (zget z (n + 2)) 0 (-zget z (n + 1)) (-zget z (n + 1) - zget z n)
    (yN z (n + 2))
  rw [zero_add] at ht
  rw [h1, h3, h4, ht, A3, ENNReal.ofReal_toReal]
  exact ne_top_of_le_ne_top (by rw [volume_disk_one]; exact ENNReal.ofReal_ne_top) (measure_mono sdiff_subset)

/-- the prefix bound by induction on the number of disks (at least three disks) -/
lemma volume_prefix_le3 (z : Fin m → Pt) : ∀ n : ℕ,
    volume (⋃ i ∈ Finset.range (n + 3), disk (yN z i) 1) ≤
      ENNReal.ofReal (π + A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 (n + 2), x3 z j)
  | 0 => by
    have h := volume_prefix_le z 1
    have e : ∑ j ∈ Finset.Ico 1 (0 + 2), x3 z j = ∑ j ∈ Finset.Ico 1 (1 + 1), A2 (zget z (j - 1)) (zget z j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj1 : j = 1 := by simp only [Finset.mem_Ico] at hj; omega
      subst hj1
      simp [x3]
    rw [e]
    exact h
  | n + 1 => by
    have ih := volume_prefix_le3 z n
    have e : (⋃ i ∈ Finset.range (n + 1 + 3), disk (yN z i) 1) ⊆ (⋃ i ∈ Finset.range (n + 3), disk (yN z i) 1) ∪
        (disk (yN z (n + 3)) 1 \ (disk (yN z (n + 2)) 1 ∪ disk (yN z (n + 1)) 1 ∪ disk (yN z n) 1)) := by
      intro p hp
      simp only [Finset.mem_range, mem_iUnion] at hp
      obtain ⟨i, hi, hp⟩ := hp
      by_cases hin : i < n + 3
      · exact Or.inl (mem_biUnion (Finset.mem_range.2 hin) hp)
      · have hi3 : i = n + 3 := by omega
        subst hi3
        by_cases h1 : p ∈ disk (yN z (n + 2)) 1 ∪ disk (yN z (n + 1)) 1 ∪ disk (yN z n) 1
        · rcases h1 with (h1 | h1) | h1
          · exact Or.inl (mem_biUnion (Finset.mem_range.2 (by omega)) h1)
          · exact Or.inl (mem_biUnion (Finset.mem_range.2 (by omega)) h1)
          · exact Or.inl (mem_biUnion (Finset.mem_range.2 (by omega)) h1)
        · exact Or.inr ⟨hp, h1⟩
    have hnn : 0 ≤ π + A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 (n + 2), x3 z j := by
      have := A1_nonneg (zget z 0)
      have : 0 ≤ ∑ j ∈ Finset.Ico 1 (n + 2), x3 z j := Finset.sum_nonneg fun j _ => x3_nonneg z j
      linarith [Real.pi_pos]
    have hx : x3 z (n + 2) = A3 (zget z n) (zget z (n + 1)) (zget z (n + 2)) := by
      simp only [x3, show n + 2 ≠ 1 by omega, ↓reduceIte, show n + 2 - 2 = n by omega,
        show n + 2 - 1 = n + 1 by omega]
    calc volume (⋃ i ∈ Finset.range (n + 1 + 3), disk (yN z i) 1)
        ≤ volume (⋃ i ∈ Finset.range (n + 3), disk (yN z i) 1) +
            volume (disk (yN z (n + 3)) 1 \ (disk (yN z (n + 2)) 1 ∪ disk (yN z (n + 1)) 1 ∪ disk (yN z n) 1)) :=
          (measure_mono e).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (π + A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 (n + 2), x3 z j) +
            ENNReal.ofReal (A3 (zget z n) (zget z (n + 1)) (zget z (n + 2))) := by
          rw [volume_new3]; exact add_le_add ih le_rfl
      _ = ENNReal.ofReal (π + A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 (n + 1 + 2), x3 z j) := by
          rw [← ENNReal.ofReal_add hnn (A3_nonneg _ _ _)]
          congr 1
          rw [show n + 1 + 2 = n + 2 + 1 from rfl, Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 2), hx]
          ring

/-- the window-3 area bound `A(y(z)) ≤ π + X_3(z)` -/
theorem unionArea_psum_le3 (z : Fin m → Pt) : unionArea (psum z) ≤ π + Xsum3 z := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · -- at most one increment: `X_3 = X`
    have e : Xsum3 z = Xsum z := by
      rw [Xsum3_eq]
      unfold Xsum
      rw [Finset.Ico_eq_empty_of_le (by omega : m ≤ 1), Finset.sum_empty, Finset.sum_empty]
    rw [e]
    exact unionArea_psum_le z
  · have hU : (⋃ i, disk (psum z i) 1) = ⋃ i ∈ Finset.range (m + 1), disk (yN z i) 1 := by
      ext p
      simp only [mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨i, hi⟩; exact ⟨i.val, i.isLt, by rwa [← psum_eq_yN]⟩
      · rintro ⟨i, hi, hp⟩; exact ⟨⟨i, hi⟩, by rwa [psum_eq_yN]⟩
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    have h : volume (⋃ i ∈ Finset.range (n + 2 + 1), disk (yN z i) 1) ≤
        ENNReal.ofReal (π + A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 (n + 2), x3 z j) := volume_prefix_le3 z n
    have hnn : 0 ≤ π + A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 (n + 2), x3 z j := by
      have := A1_nonneg (zget z 0)
      have : 0 ≤ ∑ j ∈ Finset.Ico 1 (n + 2), x3 z j := Finset.sum_nonneg fun j _ => x3_nonneg z j
      linarith [Real.pi_pos]
    unfold unionArea
    rw [hU, Xsum3_eq]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_ofReal hnn] at this
    linarith

end BHH.W3.Lap
