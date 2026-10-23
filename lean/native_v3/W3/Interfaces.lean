/-
Interfaces between the proof modules of `W3/` (the window-3 bound), as named `Prop`s.  Each module
proves its `Prop`s in its own file; the assembly (`W3/Glue3.lean`, `W3/Final3Of.lean`) uses them.

* The automaton: `PassSound3` (the pass value of `W3C` is at most `2 · Val3` of the graph of its inputs) and `Lemma1`
  (`0 ≤ Val3 H ≤ dcG G` for `H ≤ G`).  File `W3/PassSound3.lean`: `theorem passSound3 : PassSound3`,
  `theorem lemma1 : Lemma1`.
* Laplace: `LaplaceBound3 k` (sorted coordinates, window-3 area bound `A ≤ π + X_3`, Laplace transform,
  Tonelli).  File `W3/Laplace3.lean`: `theorem laplaceBound3 (k : ℕ) : LaplaceBound3 k`.
* Discretisation: `DiscBound3 g` (Jensen per product cell, marginals of the product of uniform measures, sure
  edges, the pass through `PassSound3` and `Lemma1`).  File `W3/Disc3.lean`:
  `theorem discBound3 (hP : PassSound3) (hL : Lemma1) (g : GridR) : DiscBound3 g`.
* Triple tables: `TripleSound` (the entries `W3C.tripleEntryF` in the relative frame), `LV3Sound` (the lower
  bound `W3C.lv3LoF`), `RotA3` and `ReflA3` (rotation and reflection invariance), and the primitives
  `CosSinTSound`, `AsinTSound`, `TriRangeSound`.  Files `W3/TriplePrim*.lean`: `theorem cosSinTSound`,
  `theorem asinTSound`, `theorem triRangeSound`, `theorem rotA3`, `theorem reflA3`; files `W3/TripleEntry*.lean`:
  `theorem lv3Sound (hCS : CosSinTSound) (hAS : AsinTSound) : LV3Sound` and
  `theorem tripleSound (hCS : CosSinTSound) (hAS : AsinTSound) (hTR : TriRangeSound) : TripleSound`.  The proven
  W2 table modules (T1-T8 of `W2/TabProps.lean`, `TabB.*`, `pairMean`, `sectorCen`, `rotA2`, ...) may be used.
* Recursion: `RecSound3` (the outputs of `W3C.runT3` bound `Psid3` for the table data `discOf3` of the
  computation: the exact recursion unrolled to the sum over cell sequences, its mirror symmetry, and the directed
  integer arithmetic).  Files `W3/Rec*.lean`: `theorem recSound3 : RecSound3`.
* t-integral: W2's `TIntBound` (proved in `W2/TIntSound.lean`) applies to `Psid3` (a positive exponential sum).
-/
import W3.Defs
import W2.TabProps
import W2.TSProps
import W3Cert.Rec3

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace BHH.W3

open BHH BHH.W2 W2C BHH.Cert

/-! ## The automaton -/

/-- The window-3 pass is sound: twice `Val3` of the graph of its inputs bounds its value. -/
def PassSound3 : Prop :=
  ∀ (aN aS aT : ℕ → Bool) (k : ℕ), 2 ≤ k → (passVal3 aN aS aT k : ℝ) ≤ 2 * Val3 (seqGraph3 aN aS aT k)

/-- The value bound: for a spanning subgraph `H ≤ G` on `k ≥ 2` vertices, `0 ≤ Val3 H ≤ g(G)`. -/
def Lemma1 : Prop :=
  ∀ (k : ℕ) (H G : SimpleGraph (Fin k)), H ≤ G → 2 ≤ k → 0 ≤ Val3 H ∧ Val3 H ≤ dcG G

/-! ## Laplace -/

/-- Sorted coordinates, the window-3 area bound, the Laplace transform and Tonelli:
`C_k ≥ (1/2) ∫_0^∞ t^{k-3/2} e^{-π t} Φ_k(t) dt`. -/
def LaplaceBound3 (k : ℕ) : Prop :=
  3 ≤ k →
    ENNReal.ofReal (1 / 2) *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ ((k : ℝ) - 3 / 2) * Real.exp (-(π * t))) * Psi3 (k - 1) t
      ≤ C k

/-! ## Discretisation -/

/-- Discretisation (Jensen per product cell): `Φ^d_k(t) ≤ Φ_k(t)`. -/
def DiscBound3 (g : GridR) : Prop :=
  ∀ (hNR : 0 < g.NR) (hNT : 0 < g.NT) (D : DiscData3), TableSound3 g D →
    ∀ (m : ℕ), 2 ≤ m → ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal (Psid3 g hNR hNT D m t) ≤ Psi3 m t

/-! ## Triple tables -/

/-- The relative-frame cell `(ir, slot j)` of a grid: the sector `r_ir < |z| < r_{ir+1}`, `j h < arg z < (j + 1) h`,
`h = π / NT` (the frame of the table entries; slot `0` is the first cell of a pair or a triple). -/
def rcell (g : W2C.Grid) (ir : ℕ) (j : ℤ) : Set Pt :=
  sector ((gR g).rad ir) ((gR g).rad (ir + 1)) (j * (π / g.NT)) ((j + 1) * (π / g.NT))

/-- the area of a relative cell, as a real number -/
def vr (g : W2C.Grid) (ir : ℕ) (j : ℤ) : ℝ := (volume (rcell g ir j)).toReal

/-- The grid conditions of the soundness statements (as in W2's `TableSoundOf`), with the ring test `ringOK` and a
positive lower end of the enclosure `ch` of `cos(dθ/2)` (the apex `r2 / cos(dθ/2)` of the outer pentagons divides by it;
one `cosIvG` evaluation, checked for the grid by computation). -/
def GridOK (g : W2C.Grid) : Prop :=
  0 < g.N1 ∧ 0 < g.N2 ∧ 2 ≤ g.NT ∧ g.NT ≤ 2 ^ 30 ∧ 0 < g.NSUB ∧ (∀ j, j < g.NR → ringOK g j = true) ∧
    0 < (W2C.mkAData g).ch.lo

/-- D1: the lower bound `LV3LO(ir, ir2, d)` of the mean of `|B(-z-z') ∪ B(-z') ∪ B(0)|` over `Z × Z'`,
`Z = (ir, 0)`, `Z' = (ir2, d)` (two-sided vertex lemma, or the fallback `π + E u(|z'|)`). -/
def LV3Sound : Prop :=
  GreenFormula → VertexLemmaSeg →
  ∀ g : W2C.Grid, GridOK g → ∀ (ir ir2 : ℕ) (d : ℤ), ir < g.NR → ir2 < g.NR → |d| < g.NT →
    fx (W3C.lv3LoF (W3C.mkTabData g) ir ir2 d) * vr g ir 0 * vr g ir2 d ≤
      ∫ p in rcell g ir 0 ×ˢ rcell g ir2 d, unionArea ![-(p.1 + p.2), -p.2, (0 : Pt)]

/-- D2: the triple entry `(ia, ib, ic, dab, dbc)` (`Z_a = (ia, 0)`, `Z_b = (ib, dab)`, `Z_c = (ic, dab + dbc)`, all
angular offsets of absolute value `< NT`), given the pair entry `pbc` of `(ib, ic, dbc)` with a valid `ā_2` (in its own
frame `(ib, 0)`, `(ic, dbc)`) and the pair entry `pab` of `(ia, ib, dab)` with a valid `LV3LO`: the T class means
`|z_a + z_b + z_c| ≤ 1` on `Z_a × Z_b × Z_c`, and the mean of `A_3` over it is at most `ā_3`. -/
def TripleSound : Prop :=
  GreenFormula → VertexLemmaSeg →
  ∀ g : W2C.Grid, GridOK g →
  ∀ (ia ib ic : ℕ) (dab dbc : ℤ) (pbc pab : W3C.PairE), ia < g.NR → ib < g.NR → ic < g.NR →
    |dab| < g.NT → |dbc| < g.NT → |dab + dbc| < g.NT →
    ∫ p in rcell g ib 0 ×ˢ rcell g ic dbc, A2 p.1 p.2 ≤ fx pbc.abar2 * vr g ib 0 * vr g ic dbc →
    fx pab.lv3 * vr g ia 0 * vr g ib dab ≤
      ∫ p in rcell g ia 0 ×ˢ rcell g ib dab, unionArea ![-(p.1 + p.2), -p.2, (0 : Pt)] →
    ((W3C.tripleEntryF (W3C.mkTabData g) ia ib ic dab dbc pbc pab).tcls = true →
        ∀ u ∈ rcell g ia 0, ∀ v ∈ rcell g ib dab, ∀ w ∈ rcell g ic (dab + dbc), sqDist (u + v + w) 0 ≤ 1) ∧
    ∫ p in rcell g ia 0 ×ˢ (rcell g ib dab ×ˢ rcell g ic (dab + dbc)), A3 p.1 p.2.1 p.2.2 ≤
      fx (W3C.tripleEntryF (W3C.mkTabData g) ia ib ic dab dbc pbc pab).abar3 *
        vr g ia 0 * vr g ib dab * vr g ic (dab + dbc)

/-- D3: rotating a triple of sectors by `φ` (all angles in `[-π, π]`) keeps the integral of `A_3`. -/
def RotA3 : Prop :=
  ∀ (r1 r2 a b q1 q2 a' b' s1 s2 a'' b'' φ : ℝ), 0 ≤ r1 → 0 ≤ q1 → 0 ≤ s1 →
    -π ≤ a → b ≤ π → -π ≤ a' → b' ≤ π → -π ≤ a'' → b'' ≤ π →
    -π ≤ a + φ → b + φ ≤ π → -π ≤ a' + φ → b' + φ ≤ π → -π ≤ a'' + φ → b'' + φ ≤ π →
    ∫ p in sector r1 r2 a b ×ˢ (sector q1 q2 a' b' ×ˢ sector s1 s2 a'' b''), A3 p.1 p.2.1 p.2.2 =
      ∫ p in sector r1 r2 (a + φ) (b + φ) ×ˢ (sector q1 q2 (a' + φ) (b' + φ) ×ˢ sector s1 s2 (a'' + φ) (b'' + φ)),
        A3 p.1 p.2.1 p.2.2

/-- D4: reflecting a triple of sectors in the real axis (angles `(a, b) ↦ (-b, -a)`, all in `[-π, π]`) keeps the
integral of `A_3`, and maps the points of the sectors to their conjugates (so `|u + v + w|` is unchanged). -/
def ReflA3 : Prop :=
  ∀ (r1 r2 a b q1 q2 a' b' s1 s2 a'' b'' : ℝ), 0 ≤ r1 → 0 ≤ q1 → 0 ≤ s1 →
    -π ≤ a → b ≤ π → -π ≤ a' → b' ≤ π → -π ≤ a'' → b'' ≤ π →
    (∫ p in sector r1 r2 a b ×ˢ (sector q1 q2 a' b' ×ˢ sector s1 s2 a'' b''), A3 p.1 p.2.1 p.2.2 =
      ∫ p in sector r1 r2 (-b) (-a) ×ˢ (sector q1 q2 (-b') (-a') ×ˢ sector s1 s2 (-b'') (-a'')),
        A3 p.1 p.2.1 p.2.2) ∧
    ∀ z : Pt, z ∈ sector r1 r2 a b ↔ (z.1, -z.2) ∈ sector r1 r2 (-b) (-a)

/-- D5: the table-based `cos`/`sin` of the triple entries is sound. -/
def CosSinTSound : Prop := CosSinSound (W3C.cosSinT W3C.mkCsTab)

/-- D6: the tabulated `arcsin` bounds: `asinLoT ≤ arcsin` for arguments `≥ 0`, `arcsin ≤ asinHiT` everywhere
(fixed point `fx`, Mathlib's `Real.arcsin`, which is `π/2` beyond `1`). -/
def AsinTSound : Prop :=
  (∀ a : ℤ, 0 ≤ a → fx (W3C.asinLoT W3C.mkAsinTab a) ≤ Real.arcsin (fx a)) ∧
  (∀ a : ℤ, Real.arcsin (fx a) ≤ fx (W3C.asinHiT W3C.mkAsinTab a))

/-- D7: the pentagon ranges of three relative cells (`(ia, 0)`, `(ib, dab)`, `(ic, dab + dbc)`, angular offsets of
absolute value `< NT`): `triRange28` of their scalar pentagon boxes bounds `|u + v + w|` for all points of the closed
convex hulls of the cells (the vertex lemma needs the range along segments from the centroids), both ends. -/
def TriRangeSound : Prop :=
  ∀ g : W2C.Grid, GridOK g → ∀ (ia ib ic : ℕ) (dab dbc : ℤ), ia < g.NR → ib < g.NR → ic < g.NR →
    |dab| < g.NT → |dbc| < g.NT → |dab + dbc| < g.NT →
    ∀ u ∈ closure (convexHull ℝ (rcell g ia 0)), ∀ v ∈ closure (convexHull ℝ (rcell g ib dab)),
      ∀ w ∈ closure (convexHull ℝ (rcell g ic (dab + dbc))),
      fx (W3C.triRange28 (W3C.geoAt g (W3C.mkTabData g).geo ia 0).pv (W3C.geoAt g (W3C.mkTabData g).geo ib dab).pv
          (W3C.geoAt g (W3C.mkTabData g).geo ic (dab + dbc)).pv).1 ≤ enorm2 (u + v + w) ∧
      enorm2 (u + v + w) ≤
        fx (W3C.triRange28 (W3C.geoAt g (W3C.mkTabData g).geo ia 0).pv (W3C.geoAt g (W3C.mkTabData g).geo ib dab).pv
          (W3C.geoAt g (W3C.mkTabData g).geo ic (dab + dbc)).pv).2

/-! ## Recursion -/

/-- The real table data of the computation at grid `g` and `dtl`, as used by `W3C.runT3`: per ring the cell area
rounded down and the first-step exponent rounded up to a multiple of `2^-dtl`; the symmetrised pair table (exponent
clamped at `0` and rounded up to a multiple of `2^-dtl`); the triple table (`ā_3 = a48 · 2^-48` and the T class
from the stored value `2 · a48 + T`). -/
def discOf3 (g : W2C.Grid) (dtl : ℕ) : DiscData3 :=
  let td := W3C.mkTabData g
  let pairs := W3C.mkPairs td false
  let tri := W3C.mkTri td pairs false
  let off : ℤ := ((g.NT - 1 : ℕ) : ℤ)
  let pidx (ir ir2 : ℕ) (d : ℤ) : ℕ := (ir * g.NR + ir2) * g.ND + (d + off).toNat
  let tidx (ia ib ic : ℕ) (dab dbc : ℤ) : ℕ :=
    (((ib * g.NR + ic) * g.ND + (dbc + off).toNat) * g.NR + ia) * g.ND + (dab + off).toNat
  { w := fun ir => ((td.rings[ir]!.areaLo.toNat : ℕ) : ℝ) / 2 ^ PR
    ub := fun ir => fx (W3C.upq td.rings[ir]!.euHi dtl)
    ab := fun ir ir2 d => fx (W3C.upq (max pairs[pidx ir ir2 d]!.abar2 0) dtl)
    sc := fun ir ir2 d => pairs[pidx ir ir2 d]!.scls
    nf := fun ir => td.rings[ir]!.nflag
    a3 := fun ia ib ic dab dbc => ((tri[tidx ia ib ic dab dbc]! / 2 : ℕ) : ℝ) / 2 ^ 48
    tc := fun ia ib ic dab dbc => tri[tidx ia ib ic dab dbc]! % 2 == 1 }

/-- The value `m · 2^-e` of an output entry `(m, e)` of `W3C.runT3` (entry `k - 3` is `Φ_k`). -/
def outVal (o : List (ℕ × ℤ)) (k : ℕ) : ℝ := ((o.getD (k - 3) (0, 0)).1 : ℝ) * (2 : ℝ) ^ (-(o.getD (k - 3) (0, 0)).2)

/-- E: for `t_j = j 2^-dtl` and `3 ≤ k ≤ kmax`, the lower recursion of `W3C.runT3` is at most `Φ^d_k(t_j)` for the
data `discOf3 g dtl`, and the upper recursion at least (grid with `NT` even; first-step exponents `≥ 0`). -/
def RecSound3 : Prop :=
  ∀ (g : W2C.Grid) (dtl kmax j : ℕ) (par : Bool) (hNR : 0 < (gR g).NR) (hNT : 0 < (gR g).NT),
    2 ≤ g.NT → g.NT % 2 = 0 → 3 ≤ kmax → 1 ≤ j → dtl ≤ 48 →
    (∀ ir : ℕ, 0 ≤ W3C.upq ((W3C.mkTabData g).rings[ir]!).euHi dtl) →
    ∀ k, 3 ≤ k → k ≤ kmax →
      outVal (W3C.runT3 (W3C.mkRun3 g dtl par) true j dtl kmax par) k ≤
        Psid3 (gR g) hNR hNT (discOf3 g dtl) (k - 1) ((j : ℝ) / 2 ^ dtl) ∧
      Psid3 (gR g) hNR hNT (discOf3 g dtl) (k - 1) ((j : ℝ) / 2 ^ dtl) ≤
        outVal (W3C.runT3 (W3C.mkRun3 g dtl par) false j dtl kmax par) k

end BHH.W3
