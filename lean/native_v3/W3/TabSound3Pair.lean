/-
The pair/ring part of the window-3 table soundness: W2's `TableSound` for the data `discOf3` (cell weights, first-step
exponents, the symmetrised pair table, the sure classes), from W2's `TSO.tableSoundOf` (the raw entries) and the
facts that the symmetrisation only weakens (`ā_2` the larger of the entries at `d` and `-d`, the S class the AND).
-/
import W3.TabSound3Idx
import W2.TabT14
import W2.TabPairMean
import W2.TabA
import W2.TabCen
import W2.TabRot

open MeasureTheory Set Real

namespace BHH.W3.TabSound3

open W2C BHH.Cert BHH BHH.W2

/-- W2's entry bound for a grid passing the nondegeneracy check (all W2 table facts plugged in). -/
lemma entryBound3 (hG : GreenFormula) (hV : VertexLemmaSeg) {g : Grid} (hok : GridOK g) (hnd : nondegOK g = true) :
    EntryBound g := by
  obtain ⟨h1, h2, hNT, hNT30, hNS, -, -⟩ := hok
  exact entryBound_of hV hG TabB.ringSound TabB.angleSound TabB.angleRange TabB.frangeSound TabB.distSound
    a1Radial a2Union a2LeA1 pairMean sectorCen h1 h2 hNT hNT30 hNS hnd

/-- W2's table soundness for the raw table of the grid. -/
lemma tableSoundW2 (hG : GreenFormula) (hV : VertexLemmaSeg) {g : Grid} (dtl : ℕ) (hok : GridOK g)
    (hnd : nondegOK g = true) :
    TableSound (gR g) (discOf g (mkRunData g dtl true).rings (mkRunData g dtl true).tab dtl) := by
  have hEB := entryBound3 hG hV hok hnd
  obtain ⟨h1, h2, hNT, hNT30, hNS, hring, -⟩ := hok
  exact TSO.tableSoundOf hG TabB.ringSound TabB.angleSound TabB.angleRange TabB.frangeSound a1Radial rotA2
    g dtl h1 h2 hNT hNT30 hNS hring hEB

/-- the symmetrised pair entry of `discOf3` -/
lemma discOf3_pair (g : Grid) (dtl : ℕ) {ir ir2 : ℕ} (hir : ir < g.NR) (hir2 : ir2 < g.NR) {d : ℤ}
    (hd : |d| < g.NT) :
    (discOf3 g dtl).ab ir ir2 d =
      fx (W3C.upq (max (W3C.symPair (W3C.pairEntryF (W3C.mkTabData g) ir ir2 d)
        (W3C.pairEntryF (W3C.mkTabData g) ir ir2 (-d))).abar2 0) dtl) ∧
    (discOf3 g dtl).sc ir ir2 d = (W3C.symPair (W3C.pairEntryF (W3C.mkTabData g) ir ir2 d)
        (W3C.pairEntryF (W3C.mkTabData g) ir ir2 (-d))).scls := by
  constructor
  · simp only [discOf3]
    rw [mkPairs_getD g hir hir2 hd]
  · simp only [discOf3]
    rw [mkPairs_getD g hir hir2 hd]

/-- The pair/ring part: W2's `TableSound` for the data `discOf3`. -/
theorem pairPart (hG : GreenFormula) (hV : VertexLemmaSeg) {g : Grid} (dtl : ℕ) (hok : GridOK g)
    (hnd : nondegOK g = true) : TableSound (gR g) (discOf3 g dtl).toDiscData := by
  have hW := tableSoundW2 hG hV dtl hok hnd
  obtain ⟨h1, h2, hNT, hNT30, hNS, hring, -⟩ := hok
  have hNR : (gR g).NR = g.NR := rfl
  have hNTe : (gR g).NT = g.NT := rfl
  refine ⟨hW.w_nonneg, hW.w_le, hW.ub, ?_, ?_, hW.nf⟩
  · -- ab
    intro ir ir2 it it2 hir hir2 hit hit2
    refine (hW.ab ir ir2 it it2 hir hir2 hit hit2).trans ?_
    rw [hNR] at hir hir2; rw [hNTe] at hit hit2
    set d : ℤ := (it2 : ℤ) - it with hd
    have hdlt : |d| < g.NT := by rw [hd, abs_lt]; constructor <;> omega
    have hdlt' : |-d| < g.NT := by rwa [abs_neg]
    have hab : (discOf g (mkRunData g dtl true).rings (mkRunData g dtl true).tab dtl).ab ir ir2 d =
        fx (ubInt (max (entryF g.prune ((Array.range g.NR).map (mkRing g)) (mkAData g) (mkDData g d) ir ir2).2 0)
          dtl) := by
      show fx (mkRunData g dtl true).tab[tidx g ir ir2 d]!.2 = _
      rw [hd, TSO.tab_entry g dtl hir hir2 hit hit2]
      rfl
    rw [hab, (discOf3_pair g dtl hir hir2 hdlt).1, pairEntryF_eq g hdlt, pairEntryF_eq g hdlt']
    have hv1 := ENNReal.toReal_nonneg (a := volume ((gR g).cell ir it))
    have hv2 := ENNReal.toReal_nonneg (a := volume ((gR g).cell ir2 it2))
    apply mul_le_mul_of_nonneg_right _ hv2
    apply mul_le_mul_of_nonneg_right _ hv1
    apply fx_le_iff.mpr
    exact upq_mono (le_trans (le_max_left _ _) (le_max_left _ _)) dtl
  · -- sc
    intro ir ir2 it it2 hir hir2 hit hit2 hsc
    apply hW.sc ir ir2 it it2 hir hir2 hit hit2
    rw [hNR] at hir hir2; rw [hNTe] at hit hit2
    set d : ℤ := (it2 : ℤ) - it with hd
    have hdlt : |d| < g.NT := by rw [hd, abs_lt]; constructor <;> omega
    have hdlt' : |-d| < g.NT := by rwa [abs_neg]
    rw [(discOf3_pair g dtl hir hir2 hdlt).2, pairEntryF_eq g hdlt, pairEntryF_eq g hdlt'] at hsc
    simp only [W3C.symPair, Bool.and_eq_true] at hsc
    show ((mkRunData g dtl true).tab[tidx g ir ir2 d]!.1 == 1) = true
    rw [hd, TSO.tab_entry g dtl hir hir2 hit hit2]
    exact hsc.1

end BHH.W3.TabSound3
