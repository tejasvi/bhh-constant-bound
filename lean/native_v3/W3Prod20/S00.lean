/-
Shard 0 of 1 of the grid: the run data, both directed recursions for every claimed t_j with
j > 0, and the check of their claims (native).
-/
import W3Cert.Rec3
import W3Prod20.Grid
import W3Prod20.Claims

namespace W3Prod20

theorem shard00 : W3C.shard3OK grid dtl kmax true (claims.filter (fun c => decide (0 < c.1))) = true := by
  native_decide

end W3Prod20
