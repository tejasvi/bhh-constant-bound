/-
The window-3 bound at the grid (20,10,48): `Σ_{k=6}^{22} C_k ≥ num/den` under Green's formula and the
vertex lemma, from the proof modules in `W3/` and the native checks of this package (1 claims shard, the
t-integral of the claims, the nondegeneracy of the pair entries and the enclosure of cos(dθ/2)).
-/
import W3.Final3Of
import W3.Assembly
import W3.PassSound3
import W3.Laplace3
import W3.Disc3
import W3.TriplePrimCos
import W3.TriplePrimAsin
import W3.TriplePrimGeo
import W3.TriplePrimRot
import W3.TripleEntryLV3
import W3.TripleEntryTri
import W3.TabSound3
import W2.EntryBoundPf
import W3.RecSound3
import W3Prod20.S00
import W3Prod20.TInt
import W3Prod20.Nondeg

namespace W3Prod20

open BHH BHH.W3 W2C

/-- Every claim has `j > 0`, the range of the shard. -/
theorem claims_pos : ∀ c ∈ claims, 0 < c.1 := by decide

/-- Every claim is checked by the shard. -/
theorem claimsChecked : ClaimsChecked3 grid 3 22 claims := by
  intro c hc
  exact shard3OK_spec shard00 c (List.mem_filter.mpr ⟨hc, by simp only [decide_eq_true_eq]; exact claims_pos c hc⟩)

/-- The grid conditions (decided, with the ring tests from the nondegeneracy check). -/
theorem gridOK : GridOK grid :=
  ⟨by decide, by decide, by decide, by decide, by decide, (BHH.W2.nondeg_spec nondeg).1, of_decide_eq_true chpos⟩

/-- The window-3 bound with the certified constant `num/den`. -/
theorem w3_bound : W3BoundAt ((num : ℝ) / den) :=
  w3BoundAt_of_checks passSound3 lemma1 laplaceBound3 discBound3 recSound3
    (tableSoundOf3 (tripleSound cosSinTSound asinTSound triRangeSound) (lv3Sound cosSinTSound asinTSound)
      rotA3 reflA3)
    gridOK (by decide) nondeg claimsChecked tint

/-- The same with the constant written out. -/
theorem w3_bound_lit : W3BoundAt (30379504113 / 10000000000000) := by
  have h := w3_bound
  unfold num den at h
  push_cast at h
  exact h

/-- With the box part `MainBoundsV3`: `β ≥ 5/8 + C_3 + C_4 + C_5 + num/den`, rounded down to 10 decimals. -/
theorem beta_bound (hM : MainBoundsV3) : BetaBoundV3At (6496497227 / 10 ^ 10) :=
  betaBoundV3At_of (by norm_num) (by norm_num) hM w3_bound_lit

/-- The same for the BHH constant. -/
theorem bhh_beta_bound (hM : MainBoundsV3) : BHHBetaBoundV3At (6496497227 / 10 ^ 10) :=
  bhhBetaBoundV3At_of (beta_bound hM)

end W3Prod20
