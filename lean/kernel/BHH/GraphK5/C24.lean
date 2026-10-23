import BHH.GraphK5.Local
import BHHCert.GTabK

namespace BHH.E

open BHH.Cert

set_option maxRecDepth 100000 in
theorem gtK5_c24 : localRange 5 (gtK 5).gmin 44304 1846 = true := by decide +kernel

end BHH.E
