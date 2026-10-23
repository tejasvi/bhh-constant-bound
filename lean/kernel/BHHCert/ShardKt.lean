/-
Kernel-side leaf function with the literal-table cos/sin (BHHCert/TrigTabLit.lean) and the fast untrusted candidates
(BHHCert/CandFast.lean): `LkKt k` is `LkK k` with `cosSinTabLit`, `fastCand`, `fastAsin`. Its leaf soundness
(BHH/LeafSound/FinalKt.lean) is the proof of `leafSound_K_final` with these arguments and `cosSinTabLit_sound`.
-/
import BHHCert.ShardK
import BHHCert.CandFast
import BHHCert.TrigTabLit

namespace BHH.Cert

/-- the kernel-side leaf function with the literal-table cos/sin and the fast candidates -/
def LkKt (k : Nat) (lo hi : List Int) : Int := (leafLB k (gtK k) cosSinTabLit fastCand fastAsin lo hi).val

end BHH.Cert
