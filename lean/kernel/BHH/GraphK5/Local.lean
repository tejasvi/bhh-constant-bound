/-
Kernel-only proof, k = 5: a local form of the g-table check (core Lean, kernel-friendly).  `checkTab` compares every edge
state with every completion (3^10 · 2^10 pairs for k = 5).  Here a state with an undetermined pair (base-3 digit 2)
is only compared with its two children (that digit set to 0 and to 1), and the other states with their completions;
the soundness proof (`BHH/GraphK5.lean`) is an induction on the state.
-/
import BHHCert.GTab

namespace BHH.Cert

/-- the least position `p < n` where `idx` has base-3 digit `2` -/
def firstTwo (idx : Nat) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    match firstTwo idx n with
    | some p => some p
    | none => if idx / 3 ^ n % 3 == 2 then some n else none

/-- the local check at the edge state `idx` -/
def localOK (k : Nat) (gmin : Nat → Int) (idx : Nat) : Bool :=
  match firstTwo idx (pairList k).length with
  | none => allBelow (fun e => !digitsOK idx e (pairList k).length || decide (gmin idx ≤ g2lb k e))
      (2 ^ (pairList k).length)
  | some p => decide (gmin idx ≤ gmin (idx - 2 * 3 ^ p)) && decide (gmin idx ≤ gmin (idx - 3 ^ p))

/-- the local check on the states `lo ≤ idx < lo + n` -/
def localRange (k : Nat) (gmin : Nat → Int) (lo : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => if localOK k gmin (lo + n) then localRange k gmin lo n else false

end BHH.Cert
