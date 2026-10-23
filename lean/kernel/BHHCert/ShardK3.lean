/-
The kernel-only proof, K3: the coarse kernel tree of C_5 (`5 0.6 0.0005 3e-10`, 4,194,304 initial boxes as in the paper's
C_5 runs). The decision context is untrusted (it only shapes the tree); the leaf function is `LkKt`
(BHHCert/ShardKt.lean).
-/
import BHHCert.ShardKf

namespace BHH.Cert

/-- initial-box rounds of the K3 C_5 tree: 2^22 = 4,194,304 initial boxes -/
def RNK3_5 : Nat := 22

/-- the decision context of the K3 C_5 tree (untrusted) -/
def ctxK3_5 : Flt.Ctx := Flt.mkCtx 5 0.6 0.0005 3e-10 (Float.ofBits (prefBitsN 5))

end BHH.Cert
