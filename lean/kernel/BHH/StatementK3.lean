/-
Statements of the kernel-only proof (standard axioms only), K3 = K2 plus a coarse kernel tree for C_5
(`5 0.6 0.0005 3e-10`, ninit 4194304; float lower bound 0.001406 from the search program box_ck14, 47,537,228 scored
leaves): `C_5 ≥ 0.00139` (about 1% below the float value; the Lean leaf sums are certified lower bounds), hence
(with `C_k ≥ 0` for `k ≥ 6`) `β ≥ 0.6440396`.
-/
import BHH.DefsV2

open scoped ENNReal

namespace BHH

/-- The kernel-only proof, K3: `C_3 ≥ 0.0117130195`, `C_4 ≥ 0.0059365909`, `C_5 ≥ 0.00139`. -/
def MainBoundsK3 : Prop :=
  GreenFormula → VertexLemmaSeg →
    ENNReal.ofReal (117130195 / 10 ^ 10) ≤ C 3 ∧
    ENNReal.ofReal (59365909 / 10 ^ 10) ≤ C 4 ∧
    ENNReal.ofReal (139 / 10 ^ 5) ≤ C 5

/-- The kernel-only proof, K3: every `β` with `β ≥ 5/8 + Σ_{k=3}^{30} C_k` satisfies `β ≥ 0.6440396`. -/
def BetaBoundK3 : Prop :=
  GreenFormula → VertexLemmaSeg → ∀ β : ℝ, DongCaoK30 β → (6440396 / 10 ^ 7 : ℝ) ≤ β

/-- The same for the BHH constant, with the theorem of Dong and Cao (K = 30) as a hypothesis about it. -/
def BHHBetaBoundK3 : Prop :=
  GreenFormula → VertexLemmaSeg → (∀ β : ℝ, IsBHHConstant β → DongCaoK30 β) →
    ∀ β : ℝ, IsBHHConstant β → (6440396 / 10 ^ 7 : ℝ) ≤ β

end BHH
