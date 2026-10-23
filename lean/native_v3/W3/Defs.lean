/-
Definitions of the window-3 reduction, used by the proof modules of
`W3/`.  Definitions only; nothing is assumed.

Points `y_0, ..., y_m` are given by the increments `z_j = y_{j+1} - y_j` (`j < m`), `y_0 = 0`, as in `W2/Defs.lean`.
Point `i ≥ 1` has the inputs `N = a(i, i-1)` (depends on `z_{i-1}`), `S = a(i, i-2)` (on `z_{i-2} + z_{i-1}`) and
`T = a(i, i-3)` (on `z_{i-3} + z_{i-2} + z_{i-1}`).
-/
import W2.Defs
import W2.Interfaces
import W2.Graph
import W3Cert.Auto

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W3

open BHH BHH.W2

/-! ## Areas and the integrand `Φ_k` -/

/-- `A_3(w', w, z) = |B(z,1) \ (B(0,1) ∪ B(-w,1) ∪ B(-w-w',1))|`: the new area of the disk
at `y_{j+1}` beyond the disks at `y_j`, `y_{j-1}`, `y_{j-2}`, for `(w', w, z) = (z_{j-2}, z_{j-1}, z_j)`. -/
def A3 (w' w z : Pt) : ℝ := (volume (disk z 1 \ (disk 0 1 ∪ disk (-w) 1 ∪ disk (-w - w') 1))).toReal

/-- The window-3 area bound minus `π`: `A_1(z_0) + A_2(z_0, z_1) + Σ_{2 ≤ j < m} A_3(z_{j-2}, z_{j-1}, z_j)`. -/
def Xsum3 {m : ℕ} (z : Fin m → Pt) : ℝ :=
  A1 (zget z 0) + ∑ j ∈ Finset.Ico 1 m,
    (if j = 1 then A2 (zget z 0) (zget z 1) else A3 (zget z (j - 2)) (zget z (j - 1)) (zget z j))

/-- `Φ_k(t)` with `m = k - 1` increments: `∫_{H^m} g(G_1(y(z))) e^{-t X_3(z)} dz` (in `[0, ∞]`), `g` Dong-Cao's
function `dcG`. -/
def Psi3 (m : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : Fin m → Pt, Set.indicator {z | ∀ i, z i ∈ Hp}
    (fun z => ENNReal.ofReal (dcG (unitGraph (psum z)) * Real.exp (-(t * Xsum3 z)))) z

/-! ## The window-3 pass and the value `Val3` -/

section Pass

variable (aN aS aT : ℕ → Bool)

/-- The pass on the points `0, ..., i` (the automaton `W3C.St`; the inputs of point `i` are
`[aN i, aS i, aT i]`, the edges `{i, i-1}`, `{i, i-2}`, `{i, i-3}`). -/
def runPass3 : ℕ → Option W3C.St
  | 0 => some W3C.St.init
  | i + 1 => (runPass3 i).bind fun s => s.step [aN (i + 1), aS (i + 1), aT (i + 1)]

/-- Twice the value returned by the pass on `k ≥ 2` points: the closing value at the last point `k - 1`. -/
def passVal3 (k : ℕ) : ℕ :=
  match runPass3 aN aS aT (k - 2) with
  | none => 0
  | some s => s.close2 [aN (k - 1), aS (k - 1), aT (k - 1)]

/-- Adjacency on `ℕ`: the edges `{i, i-1}` with `aN i`, `{i, i-2}` with `aS i`, `{i, i-3}` with `aT i`. -/
def seqAdj3 (a b : ℕ) : Prop :=
  (b + 1 = a ∧ aN a = true) ∨ (b + 2 = a ∧ aS a = true) ∨ (b + 3 = a ∧ aT a = true) ∨
  (a + 1 = b ∧ aN b = true) ∨ (a + 2 = b ∧ aS b = true) ∨ (a + 3 = b ∧ aT b = true)

/-- The graph on `Fin k` of the edges given by `aN`, `aS`, `aT`. -/
def seqGraph3 (k : ℕ) : SimpleGraph (Fin k) where
  Adj a b := seqAdj3 aN aS aT a.val b.val
  symm := ⟨fun _ _ h => by unfold seqAdj3 at *; tauto⟩
  loopless := ⟨fun a h => by unfold seqAdj3 at h; omega⟩

end Pass

/-- The value of a graph: `1{H connected} · max(0, 1 - u_H/2)`, `u_H` the number of vertices of degree `< 2`. -/
def Val3 {V : Type*} [Fintype V] (H : SimpleGraph V) : ℝ := by
  classical exact
    if H.Connected then max 0 (1 - ((Finset.univ.filter fun v => H.degree v < 2).card : ℝ) / 2) else 0

/-! ## Discrete data (tables) and the discrete bound `Φ^d` -/

/-- Table data of the window-3 discretisation, as real numbers: W2's data (cell weights `w`, first-step exponents
`ub`, pair exponents `ab (ir, ir', d)`, the sure classes `sc` of `{i+1, i-1}` and `nf` of `{i+1, i}`) and the triple
exponents `a3 (ia, ib, ic, dab, dbc)` with the sure class `tc` of the edge `{i+1, i-2}`. -/
structure DiscData3 extends DiscData where
  a3 : ℕ → ℕ → ℕ → ℤ → ℤ → ℝ
  tc : ℕ → ℕ → ℕ → ℤ → ℤ → Bool

/-- What the computation must guarantee about the tables: W2's `TableSound` and, for every triple of cells
`Z_a = (ia, ita)`, `Z_b = (ib, itb)`, `Z_c = (ic, itc)`, the mean of `A_3` over `Z_a × Z_b × Z_c` is at most
`a3 (ia, ib, ic, itb - ita, itc - itb)`, and a sure class `tc` means `|z_a + z_b + z_c| ≤ 1` on the whole product. -/
structure TableSound3 (g : GridR) (D : DiscData3) : Prop where
  toTableSound : TableSound g D.toDiscData
  a3 : ∀ ia ib ic ita itb itc, ia < g.NR → ib < g.NR → ic < g.NR → ita < g.NT → itb < g.NT → itc < g.NT →
    ∫ p in g.cell ia ita ×ˢ (g.cell ib itb ×ˢ g.cell ic itc), A3 p.1 p.2.1 p.2.2 ≤
      D.a3 ia ib ic ((itb : ℤ) - ita) ((itc : ℤ) - itb) * (volume (g.cell ia ita)).toReal *
        (volume (g.cell ib itb)).toReal * (volume (g.cell ic itc)).toReal
  tc : ∀ ia ib ic ita itb itc, ia < g.NR → ib < g.NR → ic < g.NR → ita < g.NT → itb < g.NT → itc < g.NT →
    D.tc ia ib ic ((itb : ℤ) - ita) ((itc : ℤ) - itb) = true →
      ∀ u ∈ g.cell ia ita, ∀ v ∈ g.cell ib itb, ∀ w ∈ g.cell ic itc, sqDist (u + v + w) 0 ≤ 1

section Seq

variable {g : GridR} {m : ℕ} (hNR : 0 < g.NR) (hNT : 0 < g.NT) (D : DiscData3) (c : CellSeq g m)

/-- The input `N` of point `i` (edge `{i, i-1}`: `|z_{i-1}| ≤ 1` sure). -/
def edgeN (i : ℕ) : Bool := edgeA1 hNR hNT D.toDiscData c i

/-- The input `S` of point `i` (edge `{i, i-2}`: `|z_{i-2} + z_{i-1}| ≤ 1` sure). -/
def edgeS (i : ℕ) : Bool := edgeA2 hNR hNT D.toDiscData c i

/-- The input `T` of point `i` (edge `{i, i-3}`: `|z_{i-3} + z_{i-2} + z_{i-1}| ≤ 1` sure). -/
def edgeT (i : ℕ) : Bool :=
  if 3 ≤ i then
    let a := cget hNR hNT c (i - 3)
    let b := cget hNR hNT c (i - 2)
    let q := cget hNR hNT c (i - 1)
    D.tc a.1.val b.1.val q.1.val (doff a b) (doff b q)
  else false

/-- The exponent bound of a cell sequence: `ub(c_0) + ab(c_0, c_1) + Σ_{2 ≤ j < m} a3(c_{j-2}, c_{j-1}, c_j)`. -/
def expoSeq3 : ℝ :=
  D.ub (cget hNR hNT c 0).1.val + ∑ j ∈ Finset.Ico 1 m,
    (if j = 1 then
      D.ab (cget hNR hNT c 0).1.val (cget hNR hNT c 1).1.val (doff (cget hNR hNT c 0) (cget hNR hNT c 1))
    else
      D.a3 (cget hNR hNT c (j - 2)).1.val (cget hNR hNT c (j - 1)).1.val (cget hNR hNT c j).1.val
        (doff (cget hNR hNT c (j - 2)) (cget hNR hNT c (j - 1))) (doff (cget hNR hNT c (j - 1)) (cget hNR hNT c j)))

end Seq

/-- `Φ^d_k(t)` (`m = k - 1`): `Σ_c (half the pass value) Π_j w(c_j) e^{-t (exponent bound)}`. -/
def Psid3 (g : GridR) (hNR : 0 < g.NR) (hNT : 0 < g.NT) (D : DiscData3) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ c : CellSeq g m, ((passVal3 (edgeN hNR hNT D c) (edgeS hNR hNT D c) (edgeT hNR hNT D c) (m + 1) : ℝ) / 2) *
    (∏ j, D.w (c j).1.val) * Real.exp (-(t * expoSeq3 hNR hNT D c))

end BHH.W3
