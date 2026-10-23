/-
Window-3 tables in exact fixed-point interval arithmetic (core Lean only), as in the C evaluator of the
window-3 certificate.

Cells: polar cells `(ir, slot j)`, radii `r_ir ≤ r ≤ r_{ir+1}` (W2's rings), angles `[j dθ, (j+1) dθ]` in a frame
relative to the first cell (rotation invariance).
* pair entries `(ir, ir2, d)` (z in `(ir, 0)`, z' in `(ir2, d)`): the S class (`|z + z'| ≤ 1` on the cells, by the polar-box bound), `ā_2`
  (W2's entry: the vertex lemma at a rounded centroid, or the fallback; W2's moments), and `LV3LO`, a lower bound of
  `E |B(-z-z') ∪ B(-z') ∪ B(0)|` (two-sided vertex lemma with the certificate's moments, or the fallback `π + E u(|z'|)`);
* triple entries `(ia, ib, ic, dab, dbc)` (z_a in `(ia, 0)`, z_b in `(ib, dab)`, z_c in `(ic, dab + dbc)`): the T class
  (`|z_a + z_b + z_c| ≤ 1` on the cells, via the outer pentagons) and `ā_3 ≥ E v3`: `min(ā_2(ib, ic, dbc),
  E[A4]_hi - LV3LO(ia, ib, dab))` with `E[A4]` by the vertex lemma for the 6 pairs, or `ā_2(ib, ic, dbc)` for far triples.
-/
import W2Cert.Table

namespace W3C
open BHH.Cert W2C

/-- centroid of the polar cell `(ring R, slot j)`: radius `R.rhoc`, direction `(j + 1/2) dθ` -/
def centroid (g : Grid) (R : Ring) (j : Int) : Iv × Iv :=
  let ang := Iv.div2e (Iv.mul (dthIv g) (Iv.int (2 * j + 1))) 1
  (Iv.mul R.rhoc (cosIvG ang), Iv.mul R.rhoc (sinIvG ang))

/-- The outer pentagon of the polar cell `(R, slot j)`: inner corners, outer corners and the apex `r2 / cos(dθ/2)` on the
mid direction (the hull of the cell lies in it). -/
def pent (g : Grid) (R : Ring) (ch : Iv) (j : Int) : Array (Iv × Iv) :=
  let dth := dthIv g
  let a1 := Iv.mul dth (Iv.int j)
  let a2 := Iv.mul dth (Iv.int (j + 1))
  let am := Iv.div2e (Iv.mul dth (Iv.int (2 * j + 1))) 1
  let (c1, s1) := (cosIvG a1, sinIvG a1)
  let (c2, s2) := (cosIvG a2, sinIvG a2)
  let (cm, sm) := (cosIvG am, sinIvG am)
  let rA := Iv.div R.r2 ch
  #[(Iv.mul R.r1 c1, Iv.mul R.r1 s1), (Iv.mul R.r1 c2, Iv.mul R.r1 s2),
    (Iv.mul R.r2 c1, Iv.mul R.r2 s1), (Iv.mul R.r2 c2, Iv.mul R.r2 s2), (Iv.mul rA cm, Iv.mul rA sm)]

/-- `(lower, upper)` bounds of `|z_a + z_b + z_c|` over three pentagons: the maximum over the 125 vertex sums, and a
separating-direction lower bound `Σ_s min_v ⟨e, v⟩ / |e|` (`e` along the sum of the vertex means; `0` if not positive). -/
def triRange (pa pb pc : Array (Iv × Iv)) : Int × Int := Id.run do
  let mut mx : Int := 0
  for p in pa do
    for q in pb do
      for r in pc do
        let sx := Iv.add (Iv.add p.1 q.1) r.1
        let sy := Iv.add (Iv.add p.2 q.2) r.2
        let v := (Iv.add (Iv.sqr sx) (Iv.sqr sy)).hi
        if v > mx then mx := v
  let mxd := (Iv.sqrt ⟨mx, mx⟩).hi
  -- direction e: midpoints of the sum of the vertex means (exact fixed-point numbers)
  let sumMid (ps : Array (Iv × Iv)) : Int × Int :=
    ps.foldl (fun (acc : Int × Int) p => (acc.1 + ivMid p.1, acc.2 + ivMid p.2)) (0, 0)
  let (ax, ay) := sumMid pa
  let (bx, by_) := sumMid pb
  let (cx, cy) := sumMid pc
  let ex := (ax + bx + cx) / 16
  let ey := (ay + by_ + cy) / 16
  -- ⟨e, v⟩ at scale 2^-2PR
  let minDot (ps : Array (Iv × Iv)) : Int :=
    ps.foldl (fun (m : Int) p =>
      let d := (Iv.add (Iv.mul p.1 (Iv.pt ex)) (Iv.mul p.2 (Iv.pt ey))).lo
      Min.min m d) ((Iv.add (Iv.mul ps[0]!.1 (Iv.pt ex)) (Iv.mul ps[0]!.2 (Iv.pt ey))).lo)
  let lo := minDot pa + minDot pb + minDot pc
  let en2 := ex * ex + ey * ey
  if lo ≤ 0 ∨ en2 == 0 then return (0, mxd)
  else
    let enHi := (Iv.sqrt ⟨shrU en2 PR, shrU en2 PR⟩).hi + 1
    -- lo / |e| at scale 2^-PR: lo is at scale 2^-(PR) · |e| (Iv.mul keeps scale 2^-PR)
    return (Max.max (divD (lo * ONE) enHi) 0, mxd)

/-- Vertex-lemma remainder of one pair at most two vertices: `2 (c_r S2 + c0 S1 + min(S2/d⁻, π S1))` with `c_r = 1/√(4 - d⁺²)`,
`c0 = 0` if `d⁺ < 1.98`, else `c_r = 0`, `c0 = 2 (asin(d⁺/2) - asin(d⁻/2))`; `S1 ≥ E X`, `S2 ≥ E X²`. `some 0` if
`d⁻ ≥ 2`, `none` if `d⁻ ≤ 0`. -/
def lvPair (dn dx S1 S2 : Int) : Option Int :=
  if 2 * ONE ≤ dn then some 0
  else if dn ≤ 0 then none
  else
    let dxIv : Iv := ⟨dx, dx⟩
    let dnIv : Iv := ⟨dn, dn⟩
    let dx2 := Iv.sqr dxIv
    let useFirst := dx * 100 < 198 * ONE ∧ dx2.hi < 4 * ONE
    let rad : Int :=
      if useFirst then
        let lam := Iv.inv (Iv.sqrt (Iv.sub (Iv.int 4) dx2))
        shrU (lam.hi * S2) PR + 1
      else
        let u := if dx < 2 * ONE then (asinIv (Iv.div2e dxIv 1)).hi else halfPiHi
        let w := (asinIv (Iv.div2e dnIv 1)).lo
        shrU (Max.max (2 * (u - w)) 0 * S1) PR + 1
    let tang := Min.min ((Iv.div ⟨S2, S2⟩ dnIv).hi) (shrU (piHi * S1) PR + 1)
    some (2 * (rad + tang))

/-- `(S1, S2)`: `E X ≤ e + Σ_s w_s √m_s =: S1`, `E X² ≤ S1²` (Minkowski), for `X = Σ_s w_s |dz_s| + e`. -/
def momentsX (ws : List Nat) (sqms : List Int) (e : Int) : Int × Int :=
  let s1 := (ws.zip sqms).foldl (fun acc (w, s) => acc + w * s) e
  (s1, shrU (s1 * s1) PR + 1)

/-- Upper bound of `|p - q|` for an interval point `p` and an exact point `q`. -/
def dist (px py : Iv) (qx qy : Int) : Int := distHi px py qx qy

/-- The range `[r1 cos(dθ/2), r2]` of `|z|` over the hull of ring `R`, widened by `e`. -/
def hullR (R : Ring) (ch : Iv) (e : Int) : Int × Int := ((Iv.mul R.r1 ch).lo - e, R.r2.hi + e)

/-- The range of `|z + z'|` over the hulls of `(R1, 0)` and `(R2, d)` (the polar-box bound on the hulls), widened by `e`. -/
def hullSum (g : Grid) (R1 R2 : Ring) (ch : Iv) (d : Int) (e : Int) : Int × Int :=
  let (cmin, cmax) := cosRange g d
  let (hmin, hmax) := frange (Iv.mul R1.r1 ch) R1.r2 (Iv.mul R2.r1 ch) R2.r2 cmin cmax
  let h0 := Max.max hmin 0
  ((Iv.sqrt ⟨h0, h0⟩).lo - e, (Iv.sqrt ⟨hmax, hmax⟩).hi + e)

/-- upper bound of `√(momHi)` -/
def sqm (R : Ring) : Int := (Iv.sqrt ⟨R.momHi, R.momHi⟩).hi

/-- A pair entry: `(S class, ā_2, LV3LO)`. -/
structure PairE where
  scls : Bool
  abar2 : Int
  lv3 : Int
  deriving Inhabited, Repr

/-- `LV3LO(ir, ir2, d)`: lower bound of `E|B(-z-z') ∪ B(-z') ∪ B(0)|`, z in `(ir, 0)`, z' in `(ir2, d)`. -/
def lv3Lo (g : Grid) (R1 R2 : Ring) (ch : Iv) (d : Int) : Int :=
  let fb := piLo + R2.euLo
  let (c0x, c0y) := centroid g R1 0
  let (c2x, c2y) := centroid g R2 d
  let px0 := Iv.add c0x c2x
  let py0 := Iv.add c0y c2y
  let p0x := -(ivMid px0)
  let p0y := -(ivMid py0)
  let p1x := -(ivMid c2x)
  let p1y := -(ivMid c2y)
  let ep0 := dist px0 py0 (-p0x) (-p0y)
  let ep1 := dist c2x c2y (-p1x) (-p1y)
  match BHH.Cert.unionArea cosSin [(p0x, p0y), (p1x, p1y), (0, 0)] ONE unionCand with
  | none => fb
  | some ur =>
    let sq := [sqm R1, sqm R2]
    -- (P0, P1): |z|; X ≤ |dz| + 2|dz'| + ep0 + ep1
    let (s1a, s2a) := momentsX [1, 2] sq (ep0 + ep1)
    let (dna, dxa) := hullR R1 ch (ep0 + ep1 + 1)
    -- (P0, P2): |z + z'|; X ≤ |dz| + |dz'| + ep0
    let (s1b, s2b) := momentsX [1, 1] sq ep0
    let (dnb, dxb) := hullSum g R1 R2 ch d (ep0 + 1)
    -- (P1, P2): |z'|; X ≤ |dz'| + ep1
    let (s1c, s2c) := momentsX [0, 1] sq ep1
    let (dnc, dxc) := hullR R2 ch (ep1 + 1)
    match lvPair dna dxa s1a s2a, lvPair dnb dxb s1b s2b, lvPair dnc dxc s1c s2c with
    | some ra, some rb, some rc =>
      let l3 := ur.A.lo - 2 * (ep0 + ep1) - (ra + rb + rc) - 2
      Max.max fb l3
    | _, _, _ => fb

/-- The pair entry `(ir, ir2, d)`. -/
def pairEntry (g : Grid) (rings : Array Ring) (ad : AData) (dd : DData) (ir ir2 : Nat) (d : Int) : PairE :=
  let (cls, ab) := entryF g.prune rings ad dd ir ir2
  ⟨cls == 1, Max.max ab 0, lv3Lo g rings[ir]! rings[ir2]! ad.ch d⟩

/-- A triple entry: `(T class, ā_3)`. -/
structure TripE where
  tcls : Bool
  abar3 : Int
  deriving Inhabited, Repr

/-- The triple entry `(ia, ib, ic, dab, dbc)`, given the pair entries `(ib, ic, dbc)` (for `ā_2`) and `(ia, ib, dab)` (for
`LV3LO`). -/
def tripleEntry (g : Grid) (rings : Array Ring) (ch : Iv) (ia ib ic : Nat) (dab dbc : Int)
    (pbc pab : PairE) : TripE :=
  let Ra := rings[ia]!
  let Rb := rings[ib]!
  let Rc := rings[ic]!
  let jb := dab
  let jc := dab + dbc
  let (mn, mx) := triRange (pent g Ra ch 0) (pent g Rb ch jb) (pent g Rc ch jc)
  let tcls := mx ≤ ONE
  let a2 := pbc.abar2
  if 2 * ONE ≤ mn then ⟨tcls, a2⟩
  else
    let (cax, cay) := centroid g Ra 0
    let (cbx, cby) := centroid g Rb jb
    let (ccx, ccy) := centroid g Rc jc
    let px0 := Iv.add cax cbx
    let py0 := Iv.add cay cby
    let p0x := -(ivMid px0)
    let p0y := -(ivMid py0)
    let p1x := -(ivMid cbx)
    let p1y := -(ivMid cby)
    let p3x := ivMid ccx
    let p3y := ivMid ccy
    let ep0 := dist px0 py0 (-p0x) (-p0y)
    let ep1 := dist cbx cby (-p1x) (-p1y)
    let ep3 := dist ccx ccy p3x p3y
    match BHH.Cert.unionArea cosSin [(p0x, p0y), (p1x, p1y), (0, 0), (p3x, p3y)] ONE unionCand with
    | none => ⟨tcls, a2⟩
    | some ur =>
      let sq := [sqm Ra, sqm Rb, sqm Rc]
      let r01 := let (s1, s2) := momentsX [1, 2, 0] sq (ep0 + ep1)
                 let (dn, dx) := hullR Ra ch (ep0 + ep1 + 1)
                 lvPair dn dx s1 s2
      let r02 := let (s1, s2) := momentsX [1, 1, 0] sq ep0
                 let (dn, dx) := hullSum g Ra Rb ch dab (ep0 + 1)
                 lvPair dn dx s1 s2
      let r03 := let (s1, s2) := momentsX [1, 1, 1] sq (ep0 + ep3)
                 lvPair (mn - (ep0 + ep3 + 1)) (mx + ep0 + ep3 + 1) s1 s2
      let r12 := let (s1, s2) := momentsX [0, 1, 0] sq ep1
                 let (dn, dx) := hullR Rb ch (ep1 + 1)
                 lvPair dn dx s1 s2
      let r13 := let (s1, s2) := momentsX [0, 1, 1] sq (ep1 + ep3)
                 let (dn, dx) := hullSum g Rb Rc ch dbc (ep1 + ep3 + 1)
                 lvPair dn dx s1 s2
      let r23 := let (s1, s2) := momentsX [0, 0, 1] sq ep3
                 let (dn, dx) := hullR Rc ch (ep3 + 1)
                 lvPair dn dx s1 s2
      match r01, r02, r03, r12, r13, r23 with
      | some a, some b, some c, some d, some e, some f =>
        let v := ur.A.hi + 2 * (ep0 + ep1 + ep3) + (a + b + c + d + e + f) - pab.lv3 + 2
        ⟨tcls, Max.max (Min.min a2 v) 0⟩
      | _, _, _, _, _, _ => ⟨tcls, a2⟩

/-! ## Fast variants (precomputed geometry, scalar pentagon ranges, tabulated `asin`, table-based `cos`/`sin`) -/

/-- scale of the scalar pentagon coordinates: `2^-SC` -/
def SC : Nat := 28

/-- outward rounding of an interval to scale `2^-SC`: `(lo, hi)` -/
def box28 (a : Iv) : Int × Int := (shrD a.lo (PR - SC), shrU a.hi (PR - SC))

/-- Per-cell geometry for slots `j ∈ [-2 NT, 2 NT]`: centroid and the pentagon as scalar boxes `(xlo, xhi, ylo, yhi)`. -/
structure Geo where
  cx : Iv
  cy : Iv
  pv : Array (Int × Int × Int × Int)
  deriving Inhabited

def mkGeo (g : Grid) (R : Ring) (ch : Iv) (j : Int) : Geo :=
  let (cx, cy) := centroid g R j
  let pv := (pent g R ch j).map fun (vx, vy) =>
    let (xl, xh) := box28 vx
    let (yl, yh) := box28 vy
    (xl, xh, yl, yh)
  ⟨cx, cy, pv⟩

/-- geometry table: index `ir * (4 NT + 1) + (j + 2 NT)` -/
def mkGeoTab (g : Grid) (rings : Array Ring) (ch : Iv) : Array Geo :=
  let W := 4 * g.NT + 1
  (Array.range (g.NR * W)).map fun q =>
    mkGeo g rings[q / W]! ch (Int.ofNat (q % W) - Int.ofNat (2 * g.NT))

def geoAt (g : Grid) (gt : Array Geo) (ir : Nat) (j : Int) : Geo :=
  gt[ir * (4 * g.NT + 1) + (j + Int.ofNat (2 * g.NT)).toNat]!

/-- `(lower, upper)` bounds of `|z_a + z_b + z_c|` over three pentagons given as scalar boxes (scale `2^-SC`), returned at
scale `2^-PR`: the maximum over the 125 vertex sums, and the separating-direction lower bound. -/
def triRange28 (pa pb pc : Array (Int × Int × Int × Int)) : Int × Int := Id.run do
  let mut mx : Int := 0
  for p in pa do
    for q in pb do
      for r in pc do
        let sxl := p.1 + q.1 + r.1
        let sxh := p.2.1 + q.2.1 + r.2.1
        let syl := p.2.2.1 + q.2.2.1 + r.2.2.1
        let syh := p.2.2.2 + q.2.2.2 + r.2.2.2
        let ax := Max.max sxl.natAbs sxh.natAbs
        let ay := Max.max syl.natAbs syh.natAbs
        let v : Int := ax * ax + ay * ay
        if v > mx then mx := v
  -- mx at scale 2^-2SC; √ at scale 2^-PR
  let mxd := (Iv.sqrt ⟨mx * 2 ^ (PR - 2 * SC), mx * 2 ^ (PR - 2 * SC)⟩).hi
  -- direction e (scale 2^-SC, divided by 16): sum of the box midpoints
  let sumMid (ps : Array (Int × Int × Int × Int)) : Int × Int :=
    ps.foldl (fun (acc : Int × Int) p => (acc.1 + (p.1 + p.2.1) / 2, acc.2 + (p.2.2.1 + p.2.2.2) / 2)) (0, 0)
  let (ax, ay) := sumMid pa
  let (bx, by_) := sumMid pb
  let (cx, cy) := sumMid pc
  let ex := (ax + bx + cx) / 16
  let ey := (ay + by_ + cy) / 16
  -- lower bound of ⟨e, v⟩ over a box (scale 2^-2SC)
  let dotLo (p : Int × Int × Int × Int) : Int :=
    (if 0 ≤ ex then ex * p.1 else ex * p.2.1) + (if 0 ≤ ey then ey * p.2.2.1 else ey * p.2.2.2)
  let minDot (ps : Array (Int × Int × Int × Int)) : Int :=
    ps.foldl (fun (m : Int) p => Min.min m (dotLo p)) (dotLo ps[0]!)
  let lo := minDot pa + minDot pb + minDot pc
  let en2 := ex * ex + ey * ey
  if lo ≤ 0 ∨ en2 == 0 then return (0, mxd)
  else
    -- |e| upper at scale 2^-SC
    let enHi : Int := (isqrtHi en2.toNat : Nat)
    -- lo / |e| at scale 2^-SC, then at scale 2^-PR (floor)
    return (Max.max ((lo * 2 ^ (PR - SC)) / enHi) 0, mxd)

/-- tabulation step of `asin`: arguments `i / 2^AK`, `0 ≤ i ≤ 2^AK` -/
def AK : Nat := 16

/-- `2^(PR - AK)` -/
def HAK : Int := 2 ^ (PR - AK)

/-- `asinTab[i]` encloses `asin(i / 2^AK)` -/
def mkAsinTab : Array Iv :=
  (Array.range (2 ^ AK + 1)).map fun i => asinIv (Iv.pt (Int.ofNat i * 2 ^ (PR - AK)))

/-- upper bound of `asin x` for `x = a / 2^PR ∈ [0, 1]`: the chord through the upper table values at the two neighbouring
nodes (`asin` is convex on `[0, 1]`); exact `asinIv` in the steep zone `x ≥ 0.98`; `π/2` for `x ≥ 1`. -/
def asinHiT (tab : Array Iv) (a : Int) : Int :=
  if ONE ≤ a then halfPiHi
  else if a ≤ 0 then (tab[0]!).hi
  else if 49 * ONE ≤ 50 * a then (asinIv (Iv.pt a)).hi
  else
    let h : Int := HAK
    let i := a / h
    let fr := a - i * h                         -- (x - x_i) at scale 2^-PR, in [0, h)
    let hi0 := (tab[i.toNat]!).hi
    let hi1 := (tab[(i + 1).toNat]!).hi
    hi0 + divU ((hi1 - hi0) * fr) h

/-- lower bound of `asin x` for `x = a / 2^PR ∈ [0, 1]`: the left secant line through the table nodes `x_{i-1}, x_i`
extended beyond `x_i` (convexity; slope bounded below by the interval data); exact in the steep zone; `x` at `x_0 = 0`. -/
def asinLoT (tab : Array Iv) (a : Int) : Int :=
  if ONE ≤ a then (tab[2 ^ AK]!).lo
  else if a ≤ 0 then 0
  else if 49 * ONE ≤ 50 * a then (asinIv (Iv.pt a)).lo
  else
    let h : Int := HAK
    let i := a / h
    let fr := a - i * h
    if i == 0 then a                            -- asin x ≥ x
    else
      let lo1 := (tab[i.toNat]!).lo
      let hi0 := (tab[(i - 1).toNat]!).hi
      lo1 + divD (Max.max (lo1 - hi0) 0 * fr) h

/-- `lvPair` with the tabulated `asin` (same formula; the two `asin` values are bracketed by table entries). -/
def lvPairT (atab : Array Iv) (dn dx S1 S2 : Int) : Option Int :=
  if 2 * ONE ≤ dn then some 0
  else if dn ≤ 0 then none
  else
    let dxIv : Iv := ⟨dx, dx⟩
    let dnIv : Iv := ⟨dn, dn⟩
    let dx2 := Iv.sqr dxIv
    let useFirst := dx * 100 < 198 * ONE ∧ dx2.hi < 4 * ONE
    let rad : Int :=
      if useFirst then
        let lam := Iv.inv (Iv.sqrt (Iv.sub (Iv.int 4) dx2))
        shrU (lam.hi * S2) PR + 1
      else
        let u := if dx < 2 * ONE then asinHiT atab (shrU dx 1) else halfPiHi
        let w := asinLoT atab (shrD dn 1)
        shrU (Max.max (2 * (u - w)) 0 * S1) PR + 1
    let tang := Min.min ((Iv.div ⟨S2, S2⟩ dnIv).hi) (shrU (piHi * S1) PR + 1)
    some (2 * (rad + tang))

/-- table step of the fast `cos`/`sin`: `2^-CK` -/
def CK : Nat := 8

/-- number of Taylor terms for `|r| ≤ 2^-(CK+1)` -/
def NT2 : Nat := 13

/-- `2^(PR - CK)` -/
def STEPC : Int := 2 ^ (PR - CK)

/-- `csTab[q + 8·2^CK]` encloses `(cos(q 2^-CK), sin(q 2^-CK))` for `|q| ≤ 8·2^CK` -/
def mkCsTab : Array (Iv × Iv) :=
  (Array.range (16 * 2 ^ CK + 1)).map fun i =>
    cosSin ((Int.ofNat i - Int.ofNat (8 * 2 ^ CK)) * 2 ^ (PR - CK))

/-- Enclosures of `(cos x, sin x)`, `x = t / 2^PR`, `|x| ≤ 8`: table value at the nearest multiple of `2^-CK` and the
angle-addition formula with a short Taylor enclosure of the remainder angle (`cosSin` outside the range). -/
def cosSinT (tab : Array (Iv × Iv)) (t : Int) : Iv × Iv :=
  if t.natAbs + 2 ^ PR ≤ 8 * ONE.toNat then
    let step : Int := STEPC
    let q := (t + step / 2) / step
    let r := t - q * step
    let (c0, s0) := tab[(q + Int.ofNat (8 * 2 ^ CK)).toNat]!
    let (c, s, last) := taylorGo r 0 NT2 (NT2 + 1) 0 (Iv.int 1) ⟨0, 0⟩ ⟨0, 0⟩
    let mag := Max.max (Int.natAbs last.lo) (Int.natAbs last.hi)
    let rem : Int := divU (mag * (NT2 + 1)) NT2 + 1
    let cr := Iv.widen c rem
    let sr := Iv.widen s rem
    let cc := Iv.sub (Iv.mul c0 cr) (Iv.mul s0 sr)
    let ss := Iv.add (Iv.mul s0 cr) (Iv.mul c0 sr)
    (clip1 cc, clip1 ss)
  else cosSin t


/-- `2^52` as a Float and `2^(PR-52)`, `2^-PR` (precomputed constants). -/
def F52 : Float := 4503599627370496.0
def SH52 : Int := 2 ^ (PR - 52)
def FSC : Float := Float.scaleB 1.0 (-(PR : Int))

/-- Float candidates for the arc endpoints (no Newton step; untrusted: the union code certifies every endpoint). -/
def FSC52 : Float := Float.scaleB 1.0 (-52 : Int)

/-- `n / 2^PR` as a Float (shift to 52 fractional bits first: `Float.ofInt` is slow on large integers) -/
@[inline] def toFF (n : Int) : Float := Float.ofInt (n >>> (PR - 52)) * FSC52

def candF : CandFn := fun wx wy _ R =>
  let fx := toFF wx
  let fy := toFF wy
  let d := Float.sqrt (fx * fx + fy * fy)
  let fR := toFF R
  let psi := Float.atan2 fy fx
  let x := d / (2 * fR)
  let al := Float.acos (if x > 1 then 1 else x)
  ((((psi - al) * F52).round.toInt64.toInt) * SH52, (((psi + al) * F52).round.toInt64.toInt) * SH52)

/-- `(√(hmin).lo, √(hmax).hi)`: the unwidened range of `|z + z'|` over the hulls of `(R1, 0)`, `(R2, d)` (see `hullSum`). -/
def hullSum0 (g : Grid) (R1 R2 : Ring) (ch : Iv) (d : Int) : Int × Int := hullSum g R1 R2 ch d 0

/-- Precomputed data of a table run. -/
structure TabData where
  g : Grid
  rings : Array Ring
  ad : AData
  ddt : Array DData
  geo : Array Geo
  atab : Array Iv
  cst : Array (Iv × Iv)
  hs : Array (Int × Int)      -- hullSum0 at index (ir * NR + ir2) * ND + (d + NT - 1)

def mkTabData (g : Grid) : TabData :=
  let rings := (Array.range g.NR).map (mkRing g)
  let ad := mkAData g
  let NR := g.NR
  let ND := g.ND
  let hs := (Array.range (NR * NR * ND)).map fun q =>
    hullSum0 g rings[q / (NR * ND)]! rings[(q / ND) % NR]! ad.ch (Int.ofNat (q % ND) - Int.ofNat (g.NT - 1))
  ⟨g, rings, ad, mkDTab g, mkGeoTab g rings ad.ch, mkAsinTab, mkCsTab, hs⟩

/-- widened hull-sum range from the table -/
def hsAt (td : TabData) (ir ir2 : Nat) (d : Int) (e : Int) : Int × Int :=
  let r := td.hs[(ir * td.g.NR + ir2) * td.g.ND + (d + Int.ofNat (td.g.NT - 1)).toNat]!
  (r.1 - e, r.2 + e)

/-- `LV3LO` with the precomputed data. -/
def lv3LoF (td : TabData) (ir ir2 : Nat) (d : Int) : Int :=
  let g := td.g
  let R1 := td.rings[ir]!
  let R2 := td.rings[ir2]!
  let ch := td.ad.ch
  let fb := piLo + R2.euLo
  let G0 := geoAt g td.geo ir 0
  let G2 := geoAt g td.geo ir2 d
  let px0 := Iv.add G0.cx G2.cx
  let py0 := Iv.add G0.cy G2.cy
  let p0x := -(ivMid px0)
  let p0y := -(ivMid py0)
  let p1x := -(ivMid G2.cx)
  let p1y := -(ivMid G2.cy)
  let ep0 := dist px0 py0 (-p0x) (-p0y)
  let ep1 := dist G2.cx G2.cy (-p1x) (-p1y)
  match BHH.Cert.unionArea (cosSinT td.cst) [(p0x, p0y), (p1x, p1y), (0, 0)] ONE candF with
  | none => fb
  | some ur =>
    let sq := [sqm R1, sqm R2]
    let (s1a, s2a) := momentsX [1, 2] sq (ep0 + ep1)
    let (dna, dxa) := hullR R1 ch (ep0 + ep1 + 1)
    let (s1b, s2b) := momentsX [1, 1] sq ep0
    let (dnb, dxb) := hsAt td ir ir2 d (ep0 + 1)
    let (s1c, s2c) := momentsX [0, 1] sq ep1
    let (dnc, dxc) := hullR R2 ch (ep1 + 1)
    match lvPairT td.atab dna dxa s1a s2a, lvPairT td.atab dnb dxb s1b s2b, lvPairT td.atab dnc dxc s1c s2c with
    | some ra, some rb, some rc =>
      let l3 := ur.A.lo - 2 * (ep0 + ep1) - (ra + rb + rc) - 2
      Max.max fb l3
    | _, _, _ => fb

/-- The pair entry with the precomputed data. -/
def pairEntryF (td : TabData) (ir ir2 : Nat) (d : Int) : PairE :=
  let g := td.g
  let (cls, ab) := entryF g.prune td.rings td.ad td.ddt[(d + Int.ofNat (g.NT - 1)).toNat]! ir ir2
  ⟨cls == 1, Max.max ab 0, lv3LoF td ir ir2 d⟩

/-- The triple entry with the precomputed data. -/
def tripleEntryF (td : TabData) (ia ib ic : Nat) (dab dbc : Int) (pbc pab : PairE) : TripE :=
  let g := td.g
  let ch := td.ad.ch
  let Ra := td.rings[ia]!
  let Rb := td.rings[ib]!
  let Rc := td.rings[ic]!
  let Ga := geoAt g td.geo ia 0
  let Gb := geoAt g td.geo ib dab
  let Gc := geoAt g td.geo ic (dab + dbc)
  let (mn, mx) := triRange28 Ga.pv Gb.pv Gc.pv
  let tcls := mx ≤ ONE
  let a2 := pbc.abar2
  if 2 * ONE ≤ mn then ⟨tcls, a2⟩
  else
    let px0 := Iv.add Ga.cx Gb.cx
    let py0 := Iv.add Ga.cy Gb.cy
    let p0x := -(ivMid px0)
    let p0y := -(ivMid py0)
    let p1x := -(ivMid Gb.cx)
    let p1y := -(ivMid Gb.cy)
    let p3x := ivMid Gc.cx
    let p3y := ivMid Gc.cy
    let ep0 := dist px0 py0 (-p0x) (-p0y)
    let ep1 := dist Gb.cx Gb.cy (-p1x) (-p1y)
    let ep3 := dist Gc.cx Gc.cy p3x p3y
    match BHH.Cert.unionArea (cosSinT td.cst) [(p0x, p0y), (p1x, p1y), (0, 0), (p3x, p3y)] ONE candF with
    | none => ⟨tcls, a2⟩
    | some ur =>
      let sq := [sqm Ra, sqm Rb, sqm Rc]
      let atb := td.atab
      let r01 := let (s1, s2) := momentsX [1, 2, 0] sq (ep0 + ep1)
                 let (dn, dx) := hullR Ra ch (ep0 + ep1 + 1)
                 lvPairT atb dn dx s1 s2
      let r02 := let (s1, s2) := momentsX [1, 1, 0] sq ep0
                 let (dn, dx) := hsAt td ia ib dab (ep0 + 1)
                 lvPairT atb dn dx s1 s2
      let r03 := let (s1, s2) := momentsX [1, 1, 1] sq (ep0 + ep3)
                 lvPairT atb (mn - (ep0 + ep3 + 1)) (mx + ep0 + ep3 + 1) s1 s2
      let r12 := let (s1, s2) := momentsX [0, 1, 0] sq ep1
                 let (dn, dx) := hullR Rb ch (ep1 + 1)
                 lvPairT atb dn dx s1 s2
      let r13 := let (s1, s2) := momentsX [0, 1, 1] sq (ep1 + ep3)
                 let (dn, dx) := hsAt td ib ic dbc (ep1 + ep3 + 1)
                 lvPairT atb dn dx s1 s2
      let r23 := let (s1, s2) := momentsX [0, 0, 1] sq ep3
                 let (dn, dx) := hullR Rc ch (ep3 + 1)
                 lvPairT atb dn dx s1 s2
      match r01, r02, r03, r12, r13, r23 with
      | some a, some b, some c, some d, some e, some f =>
        let v := ur.A.hi + 2 * (ep0 + ep1 + ep3) + (a + b + c + d + e + f) - pab.lv3 + 2
        ⟨tcls, Max.max (Min.min a2 v) 0⟩
      | _, _, _, _, _, _ => ⟨tcls, a2⟩

end W3C
