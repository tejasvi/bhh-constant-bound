/-
Soundness of the literal-table cos/sin `cosSinTabLit` (BHHCert/TrigTabLit.lean): it equals `cosSinTab` (the table rows
are `cosSin` at the grid points, BHHCert/TrigTabLitCheck.lean, and `csTable` is `cosSin` at the grid points by its
definition), whose soundness is `cosSinTab_sound` (BHH/TrigTab.lean).
-/
import BHH.TrigTab
import BHHCert.TrigTabLitCheck

namespace BHH

open BHH.Cert

theorem csLit_cosSin (j : ℕ) (hj : j < 7 * 2 ^ TB + 1) :
    ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB))) = true := by
  have hTB : TB = 8 := rfl
  rw [hTB] at hj
  have hr : j / 64 < 29 := by omega
  interval_cases h : j / 64
  · exact List.all_eq_true.1 csLit_row0 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row1 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row2 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row3 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row4 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row5 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row6 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row7 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row8 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row9 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row10 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row11 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row12 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row13 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row14 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row15 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row16 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row17 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row18 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row19 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row20 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row21 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row22 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row23 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row24 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row25 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row26 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row27 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 csLit_row28 j (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem csTable_getD (j : ℕ) (hj : j < 7 * 2 ^ TB + 1) :
    csTable.getD j csTrivial = cosSin ((j : Int) * 2 ^ (PR - TB)) := by
  simp [csTable, Array.getD, hj]

theorem csLit_eq (j : ℕ) (hj : j < 7 * 2 ^ TB + 1) : csLit j = csTable.getD j csTrivial := by
  rw [csTable_getD j hj]
  exact ivPairEqB_eq (csLit_cosSin j hj)

theorem cosSinTabLit_eq : cosSinTabLit = cosSinTab := by
  funext t
  unfold cosSinTabLit cosSinTab
  split
  · rename_i h
    have hONE : ONE.toNat = 2 ^ 96 := by decide
    have hPR : PR = 96 := rfl
    have hTB : TB = 8 := rfl
    have hj : t.natAbs >>> (PR - TB) < 7 * 2 ^ TB + 1 := by
      rw [Nat.shiftRight_eq_div_pow, hPR, hTB]
      rw [hONE] at h
      have : t.natAbs / 2 ^ 88 ≤ 7 * 2 ^ 8 := Nat.div_le_of_le_mul (by norm_num at h ⊢; omega)
      omega
    dsimp only
    rw [csLit_eq _ hj]
  · rfl

theorem cosSinTabLit_sound : CosSinSound cosSinTabLit := by
  rw [cosSinTabLit_eq]
  exact cosSinTab_sound

end BHH
