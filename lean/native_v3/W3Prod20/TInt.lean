/-
The t-integral of the claims: `Σ_{k=6}^{kmax} C_k >= num/den` (native).
-/
import W2Cert.Shard
import W3Prod20.Grid
import W3Prod20.Claims

namespace W3Prod20

theorem tint : W2C.tintOK dtl T kmax lsub claims num den = true := by
  native_decide

end W3Prod20
