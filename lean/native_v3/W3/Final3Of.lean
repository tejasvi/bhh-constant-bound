/-
The window-3 bound `W3BoundAt (num/den)` for a production grid from the proof modules (as `Prop`s, with the table
soundness `TableSoundOf3`) and the three computational checks of the run: the claims checked by both directed
recursions (`ClaimsChecked3` at `dtl = 3`, `kmax = 22`), the t-integral of the claims (`tintOK` with `T = 6`,
`lsub = 8`), and the nondegeneracy of the tables (`nondegOK`).  W2's `tIntBound` is the t-integral module; the
first-step exponents are `≥ 0` by W2's ring facts (`TabB.ringSound`), as in W2's `hub_of` (`W2/FinalOf.lean`).
-/
import W3.Glue3
import W2.TIntSound
import W2.TabT14
import W2.EntryBase
import BHH.StatementW3

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W3.Final3

open W2C BHH.Cert BHH BHH.W2

lemma meanA1_nonneg {r1 r2 : ℝ} (h0 : 0 ≤ r1) (h12 : r1 < r2) : 0 ≤ meanA1 r1 r2 := by
  unfold meanA1
  apply mul_nonneg (div_nonneg (by norm_num) (by nlinarith))
  apply intervalIntegral.integral_nonneg h12.le
  intro r hr
  exact mul_nonneg (A1c_nonneg (h0.trans hr.1)) (h0.trans hr.1)

/-- `euHi ≥ 0` for every ring of the table data (so the first-step exponents of `discOf3` are `≥ 0`). -/
lemma hub3 (hRS : RingSound) {g : Grid} (hN1 : 0 < g.N1) (hN2 : 0 < g.N2) (hNT : 2 ≤ g.NT) (hNS : 0 < g.NSUB)
    (hr : ∀ j, j < g.NR → ringOK g j = true) (dtl : ℕ) :
    ∀ ir : ℕ, 0 ≤ W3C.upq ((W3C.mkTabData g).rings[ir]!).euHi dtl := by
  intro ir
  have hrings : (W3C.mkTabData g).rings = (Array.range g.NR).map (mkRing g) := rfl
  show 0 ≤ ubInt ((W3C.mkTabData g).rings[ir]!).euHi dtl
  apply ubInt_nonneg _ dtl
  by_cases h : ir < g.NR
  · rw [hrings, rings_getElem g h]
    have hrok := hr ir h
    simp only [ringOK, Bool.and_eq_true, decide_eq_true_eq] at hrok
    obtain ⟨-, -, -, -, -, -, hhi, -⟩ := hRS g hN1 hN2 hNT hNS ir h hrok.1 hrok.2
    exact fx_nonneg_iff.mp ((meanA1_nonneg (GridR.rad_nonneg (gR g) ir) (rad_lt (gR g) hN1 hN2 ir)).trans hhi)
  · rw [getElem!_neg _ _ (by rw [hrings]; simp; omega)]
    exact le_rfl

end BHH.W3.Final3

namespace BHH.W3

open W2C BHH.Cert BHH BHH.W2

/-- **The window-3 bound for a production grid**: `Σ_{k=6}^{22} C_k ≥ num/den` from the proof modules and the
computational checks of the run on the grid `g` (`dtl = 3`, `T = 6`, `kmax = 22`, `lsub = 8`). -/
theorem w3BoundAt_of_checks (hP : PassSound3) (hL1 : Lemma1) (hLap : ∀ k, LaplaceBound3 k)
    (hD : ∀ (hP : PassSound3) (hL : Lemma1) (g : GridR), DiscBound3 g) (hRec : RecSound3) (hTSO : TableSoundOf3)
    {g : W2C.Grid} {num den : ℕ} {cs : List TClaim} (hg : GridOK g) (hev : g.NT % 2 = 0)
    (hnd : nondegOK g = true) (hcc : ClaimsChecked3 g 3 22 cs) (htint : tintOK 3 6 22 8 cs num den = true) :
    W3BoundAt ((num : ℝ) / den) := by
  intro hG hV
  have hTS := hTSO hG hV g 3 hg (by norm_num) hev hnd
  obtain ⟨hN1, hN2, hNT, -, hNS, hr, -⟩ := hg
  have hub := Final3.hub3 TabB.ringSound hN1 hN2 hNT hNS hr 3
  have hNR0 : 0 < (gR g).NR := by show 0 < g.N1 + g.N2; omega
  have hNT0 : 0 < (gR g).NT := by show 0 < g.NT; omega
  exact sum_C_ge3 tIntBound hP hL1 hLap hD hRec hNR0 hNT0 hNT hev (by norm_num) hcc htint hTS hub (by norm_num)

end BHH.W3
