/-
The grid (20,10,48) (NSUB 64, no vertex pruning) and the run parameters: dt = 2^-3, T = 6, kmax = 22,
2^8 sub-intervals per t-step; the t-integral target num/den.
-/
import W2Cert.Table

namespace W3Prod20

def grid : W2C.Grid := ⟨20, 10, 48, 64, false⟩
def dtl : Nat := 3
def T : Nat := 6
def kmax : Nat := 22
def lsub : Nat := 8
def num : Nat := 30379504113
def den : Nat := 10000000000000

end W3Prod20
