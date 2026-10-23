/-
`tableSoundOf3 : TripleSound → LV3Sound → RotA3 → ReflA3 → TableSoundOf3` (`W3/Glue3.lean`): the table soundness of the
window-3 run data `discOf3`, from the pair/ring part (`W3/TabSound3Pair.lean`, W2's proven table facts) and the
triple part (`W3/TabSound3Tri.lean`).
-/
import W3.TabSound3Tri

namespace BHH.W3

open W2C BHH.Cert BHH BHH.W2

/-- **Table soundness of the window-3 run data** (`TableSoundOf3`, `W3/Glue3.lean`) from the triple entries
(`TripleSound`), the `LV3LO` bound (`LV3Sound`) and the rotation and reflection invariance of `A_3` (`RotA3`,
`ReflA3`), with W2's proven table facts for the pair part. -/
theorem tableSoundOf3 (hTS : TripleSound) (hLV : LV3Sound) (hRot : RotA3) (hRefl : ReflA3) : TableSoundOf3 := by
  intro hG hV g dtl hok _hdtl _hev hnd
  exact ⟨TabSound3.pairPart hG hV dtl hok hnd, TabSound3.a3Part hTS hLV hRot hRefl hG hV dtl hok hnd,
    TabSound3.tcPart hTS hLV hG hV dtl hok hnd⟩

end BHH.W3

