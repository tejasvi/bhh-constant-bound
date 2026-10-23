import BHH.MainN3
import W3Prod20.Final

/-! The native proof with the window-3 bound of the grid (20,10,48): `MainBoundsV3` (k = 3, 4, 5; `BHH/MainN3.lean`) and
`W3BoundAt (30379504113 / 10 ^ 13)` (`W3Prod20/Final.lean`) give β ≥ 5/8 + C_3 + C_4 + C_5 + 0.0030379504113 ≥ 0.6496497227. -/

namespace BHH

/-- β ≥ 0.6496497227 for every β with `DongCaoK30 β`, under `GreenFormula` and `VertexLemmaSeg` -/
theorem betaBoundV3At_N_w20 : BetaBoundV3At (6496497227 / 10 ^ 10) :=
  W3Prod20.beta_bound mainBoundsV3_N

/-- the same for the BHH constant -/
theorem bhhBetaBoundV3At_N_w20 : BHHBetaBoundV3At (6496497227 / 10 ^ 10) :=
  W3Prod20.bhh_beta_bound mainBoundsV3_N

end BHH
