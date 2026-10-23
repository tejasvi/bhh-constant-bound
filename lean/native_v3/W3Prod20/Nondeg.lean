/-
The nondegeneracy check of the grid (rings and the vertex paths of the pair entries; W2) (native).
-/
import W2.EntryDefs
import W3Prod20.Grid

namespace W3Prod20

theorem nondeg : W2C.nondegOK grid = true := by
  native_decide

theorem chpos : decide (0 < (W2C.mkAData grid).ch.lo) = true := by
  native_decide

end W3Prod20
