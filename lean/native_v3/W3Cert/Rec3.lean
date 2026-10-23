/-
The window-3 transfer-operator recursion in exact integer arithmetic with
directed rounding, and the shard check for `native_decide` (core Lean only).

Cells `c = ir * NT + it` (`ir < NR`, `it < NT`, absolute angular slot), `NC = NR * NT`; the mirror image of `c` is
`R c = ir * NT + (NT - 1 - it)` (all angles negated; `NT` even).  The tables are indexed by radial indices and angular
offsets and are mirror symmetric: the pair table by conservative symmetrisation of the raw entries at `d` and `-d`
(both `S` classes, the larger `ā_2`, the smaller `LV3LO`), the triple table by computing the half
`dbc > 0 ∨ (dbc = 0 ∧ dab ≥ 0)` and copying the mirror entry `(-dab, -dbc)` into the other half (reflection
invariance of the triple entries).

Level `i ≥ 2` (points `y_0, ..., y_i` placed; cells `c_0, ..., c_{i-1}` of the increments `z_0, ..., z_{i-1}`):
`F_i(c_{i-1}, c_{i-2}, D)`, stored as sparse rows: for each current cell `cb = c_{i-1}` the nonzero entries
`(ca, D, m)`, grouped in segments of equal previous cell `ca = c_{i-2}`, value `m · 2^-E` (one exponent `E` per level).
One step:
  `F_{i+1}(cc, cb, D') = |Z_cc| Σ_{ca, D} F_i(cb, ca, D) e^{-t ā3(ca, cb, cc)} [D' = δ(D; N(cc), S(cb, cc), T(ca, cb, cc))]`,
and the closing sum `Φ_{i+2}` uses half the closing value `close2` instead of the transitions.  For the exact recursion
with mirror symmetric tables, `F_i(R cb, R ca, D) = F_i(cb, ca, D)`; so only the targets `cc` with slot `≥ NT/2` are
computed, the row of `R cc` is the row of `cc` with every previous cell `ca` replaced by `R ca`, and `Φ` (the sum over
all targets of half the closing values) is the sum over the computed half of the closing values.

Kernels: `e^{-t ā}` at scale `2^-62` for `t = t_j = j 2^-dtl`; the triple kernels are `e1^j` with `e1 = e^{-2^-dtl ā3}`
(from three tables of the 17-bit digits of `ā3 · 2^48`; binary powering, directed rounding at every product).  `lower = true` rounds every kernel, product and stored value
down (a lower bound of the exact recursion with the stored tables), `lower = false` rounds up.
-/
import W3Cert.Auto
import W3Cert.Tab3
import W2Cert.Rec
import W2Cert.TInt
import W2Cert.Shard

namespace W3C
open BHH.Cert W2C

/-! ## Constants and arithmetic -/

/-- number of automaton states (103) -/
def NS : Nat := reachable.size

/-- the pass tables with an index for "dead" (`NS`): `trs[s * 8 + i]`, `cls[s * 8 + i]` (twice the closing value),
input `i = 4 N + 2 S + T` -/
def trs : Array Nat := transTab.map fun o => o.getD NS
def cls : Array Nat := close2Tab

/-- `2^62` (not inlined: big literals are rebuilt from strings at every use) -/
@[noinline] def P62 : Nat := 2 ^ 62

/-- `2^(PR - 48)` -/
@[noinline] def Q48 : Nat := 2 ^ (PR - 48)

/-- `⌊x y / 2^62⌋` (`lower`) or `⌊x y / 2^62⌋ + 1` (an upper bound), from the 31-bit halves (all products stay
below `2^63` for `x, y ≤ 2^62`) -/
@[inline] def mul62 (lower : Bool) (x y : Nat) : Nat :=
  let x1 := x >>> 31
  let x0 := x &&& m31
  let y1 := y >>> 31
  let y0 := y &&& m31
  let f := x1 * y1 + (x1 * y0 + x0 * y1 + (x0 * y0) >>> 31) >>> 31
  if lower then f else f + 1

/-- `x^j` for `x` at scale `2^-62`, at scale `2^-62`, rounded down (`lower`) or up at every product (binary
powering) -/
def powK (lower : Bool) (x : Nat) : Nat → Nat
  | 0 => P62
  | 1 => x
  | j + 2 =>
    let h := powK lower x ((j + 2) / 2)
    let h2 := mul62 lower h h
    if (j + 2) % 2 == 0 then h2 else mul62 lower h2 x
  decreasing_by omega

/-- `a` rounded up to a multiple of `2^dtl` -/
def upq (a : Int) (dtl : Nat) : Int := a + (2 ^ dtl - a % 2 ^ dtl) % 2 ^ dtl

/-- `ā` (scale `2^-PR`, clamped at `0`) rounded up to a multiple of `2^(PR-48)`, divided by it -/
def up48 (a : Int) : Nat := (divU (Max.max a 0) (Q48 : Int)).toNat

/-- `#[f 0, ..., f (n-1)]`, computed in `nch` parallel chunks if `par` -/
@[specialize] def pgen {α : Type} [Inhabited α] (par : Bool) (nch n : Nat) (f : Nat → α) : Array α :=
  if par then
    let chunk := (n + nch - 1) / nch
    let parts := (List.range nch).map fun p => Task.spawn fun _ =>
      (Array.range (Min.min chunk (n - Min.min n (p * chunk)))).map fun i => f (p * chunk + i)
    parts.foldl (fun acc t => acc ++ t.get) #[]
  else (Array.range n).map f

/-! ## Tables -/

/-- conservative mirror symmetrisation of the pair entries at `d` and `-d` -/
def symPair (a b : PairE) : PairE := ⟨a.scls && b.scls, Max.max a.abar2 b.abar2, Min.min a.lv3 b.lv3⟩

/-- The raw pair entries, index `(ir * NR + ir2) * ND + (d + NT - 1)`, in parallel over `ir` (`par`). -/
def rawPairs (td : TabData) (par : Bool) : Array PairE :=
  let g := td.g
  let rowOf (ir : Nat) : Array PairE :=
    (Array.range (g.NR * g.ND)).map fun q =>
      pairEntryF td ir (q / g.ND) (Int.ofNat (q % g.ND) - Int.ofNat (g.NT - 1))
  let rows : List (Array PairE) :=
    if par then ((List.range g.NR).map fun ir => Task.spawn fun _ => rowOf ir).map Task.get
    else (List.range g.NR).map rowOf
  rows.foldl (· ++ ·) #[]

/-- The pair table: entry `idx` (offset index `di = idx % ND`) symmetrised with the entry at `ND - 1 - di`. -/
def mkPairs (td : TabData) (par : Bool) : Array PairE :=
  let raw := rawPairs td par
  let ND := td.g.ND
  (Array.range raw.size).map fun idx =>
    let di := idx % ND
    symPair raw[idx]! raw[idx - di + (ND - 1 - di)]!

/-- the computed half of a triple block: `dbc > 0`, or `dbc = 0` and `dab ≥ 0` (offset indices `dbcN = dbc + NT - 1`,
`dabN = dab + NT - 1`) -/
@[inline] def canon3 (NT dbcN dabN : Nat) : Bool := NT - 1 < dbcN || (dbcN == NT - 1 && NT - 1 ≤ dabN)

/-- The triple table.  Block `(ib, ic)` (blocks in the order `ib * NR + ic`) holds the entry `(dbc, ia, dab)` at
`(dbcN * NR + ia) * ND + dabN`, so the global index is `T3I = (((ib * NR + ic) * ND + dbcN) * NR + ia) * ND + dabN`.
Entries of the computed half are `2 · up48(ā3) + T` (from `tripleEntryF` with the pair entries `(ib, ic, dbc)` and
`(ia, ib, dab)`); the others are copies of the mirror entry `(-dbc, ia, -dab)`.  In parallel over blocks (`par`). -/
def mkTri (td : TabData) (pairs : Array PairE) (par : Bool) : Array Nat :=
  let g := td.g
  let NR := g.NR
  let NT := g.NT
  let ND := g.ND
  let blockOf (b : Nat) : Array Nat :=
    let ib := b / NR
    let ic := b % NR
    let half : Array Nat := (Array.range (ND * NR * ND)).map fun q =>
      let dbcN := q / (NR * ND)
      let ia := (q / ND) % NR
      let dabN := q % ND
      if canon3 NT dbcN dabN then
        let te := tripleEntryF td ia ib ic (Int.ofNat dabN - Int.ofNat (NT - 1)) (Int.ofNat dbcN - Int.ofNat (NT - 1))
          pairs[(ib * NR + ic) * ND + dbcN]! pairs[(ia * NR + ib) * ND + dabN]!
        2 * up48 te.abar3 + (if te.tcls then 1 else 0)
      else 0
    (Array.range (ND * NR * ND)).map fun q =>
      let dbcN := q / (NR * ND)
      let ia := (q / ND) % NR
      let dabN := q % ND
      if canon3 NT dbcN dabN then half[q]! else half[((ND - 1 - dbcN) * NR + ia) * ND + (ND - 1 - dabN)]!
  let blocks : List (Array Nat) :=
    if par then ((List.range (NR * NR)).map fun b => Task.spawn fun _ => blockOf b).map Task.get
    else (List.range (NR * NR)).map blockOf
  blocks.foldl (· ++ ·) #[]

/-- `ā3 · 2^PR` of a stored triple value `v = 2 · a48 + T` -/
@[inline] def a3v (v : Nat) : Int := Int.ofNat ((v / 2) * Q48)

/-- `2^17`, `2^17 - 1`, `2^51` -/
@[noinline] def P17 : Nat := 2 ^ 17
@[noinline] def M17 : Nat := 2 ^ 17 - 1
@[noinline] def P51 : Nat := 2 ^ 51

/-- Tables for `e1`: `e^{-n 2^34 2^-48 2^-dtl}`, `e^{-n 2^17 2^-48 2^-dtl}`, `e^{-n 2^-48 2^-dtl}` for `n < 2^17` (scale
`2^-62`, rounded down or up, by `kern`). -/
structure ExpTabs where
  t2 : Array Nat
  t1 : Array Nat
  t0 : Array Nat
  deriving Inhabited

def mkExpTabs (lower : Bool) (dtl : Nat) (par : Bool) : ExpTabs :=
  ⟨pgen par 64 P17 fun n => kern lower 1 dtl (Int.ofNat (n * 2 ^ (PR - 14))),
   pgen par 64 P17 fun n => kern lower 1 dtl (Int.ofNat (n * 2 ^ (PR - 31))),
   pgen par 64 P17 fun n => kern lower 1 dtl (Int.ofNat (n * Q48))⟩

/-- `e1 = e^{-2^-dtl ā3}` at scale `2^-62` (directed) for a stored triple value `v`: for `a48 = v / 2 < 2^51`, the
product of the three table values of the 17-bit digits of `a48`; otherwise `kern` directly. -/
def e1Of (lower : Bool) (dtl : Nat) (et : ExpTabs) (v : Nat) : Nat :=
  let a := v / 2
  if a < P51 then mul62 lower (mul62 lower et.t2[a >>> 34]! et.t1[(a >>> 17) &&& M17]!) et.t0[a &&& M17]!
  else kern lower 1 dtl (a3v v)

/-- Shared data of a run (all `t` and both directions): the rings, the pair table, the pair exponents rounded up to
multiples of `2^dtl`, and per triple entry `T3I` the kernels `e1 = e^{-2^-dtl ā3}` at scale `2^-62` (rounded down,
stored as `2 · e1 + T` with the T class, and rounded up). -/
structure Run3 where
  g : Grid
  rings : Array Ring
  pairs : Array PairE
  ab2 : Array Int
  e1lo : Array Nat
  e1hi : Array Nat
  deriving Inhabited

def mkRun3 (g : Grid) (dtl : Nat) (par : Bool) : Run3 :=
  let td := mkTabData g
  let pairs := mkPairs td par
  let tri := mkTri td pairs par
  let etl := mkExpTabs true dtl par
  let eth := mkExpTabs false dtl par
  let e1lo := pgen par 256 tri.size fun i => let v := tri[i]!; 2 * e1Of true dtl etl v + v % 2
  let e1hi := pgen par 256 tri.size fun i => e1Of false dtl eth tri[i]!
  ⟨g, td.rings, pairs, pairs.map fun p => upq (Max.max p.abar2 0) dtl, e1lo, e1hi⟩

/-! ## The recursion -/

/-- Read-only data of one `t` and direction. -/
structure RecData3 where
  NR : Nat
  NT : Nat
  ND : Nat
  /-- per ring: the cell area rounded down (scale `2^-PR`) -/
  w : Array Nat
  /-- per ring: `4` if the edge `{i+1, i}` is sure (`N`), else `0` -/
  nb : Array Nat
  /-- per pair index: `2` if the edge `{i+1, i-1}` is sure (`S`), else `0` -/
  sb : Array Nat
  /-- per triple index `T3I`: `2 · K + T`, `K` the kernel `e^{-t ā3}` at scale `2^-62` (directed), `T` the T class -/
  K3 : Array Nat
  deriving Inhabited

/-- A level row (current cell `cb`): the nonzero entries `(ca, D, m)` in segments of equal previous cell: segment `s`
has previous cell `segCa[s]` and entries `[segStart[s], segStart[s+1])` (states `st`, mantissas `m`). -/
structure Row where
  segCa : Array Nat
  segStart : Array Nat
  st : Array Nat
  m : Array Nat
  deriving Inhabited

/-- the empty row -/
def Row.empty : Row := ⟨#[], #[0], #[], #[]⟩

/-- `mulTop` in `UInt64`: equal to `W2C.mulTop lower (v >>> 31) (v &&& m31) k1 k0` for `v < 2^62`, `k1 < 2^32`,
`k0 < 2^31` (all products stay below `2^64`) -/
@[inline] def mulTopU (lower : Bool) (v k1 k0 : UInt64) : UInt64 :=
  let g1 := v >>> 31
  let g0 := v &&& 0x7FFFFFFF
  let t := (g1 * k1) >>> 14 + (g1 * k0 + g0 * k1) >>> 45
  if lower then t else t + 3

/-- MAC loop over the entries `[q, e)` of one segment (kernel halves `k1`, `k0`): `acc[D + off] += ⌊v K / 2^76⌋`
(directed, `mulTopU`) for every entry `(D, v)`; `off = NS · T` separates the two T classes.  The row arrays are read
with the bounds `e ≤ rst.size`, `e ≤ rm.size` checked once by the caller. -/
def macLoop (lower : Bool) (rst rm : Array Nat) (k1 k0 : UInt64) (off : Nat) (e : Nat)
    (hst : e ≤ rst.size) (hm : e ≤ rm.size) (q : Nat) (acc : Array Nat) : Array Nat :=
  if hq : q < e then
    let v := (rm[q]'(Nat.lt_of_lt_of_le hq hm)).toUInt64
    let D := rst[q]'(Nat.lt_of_lt_of_le hq hst) + off
    macLoop lower rst rm k1 k0 off e hst hm (q + 1) (acc.set! D (acc[D]! + (mulTopU lower v k1 k0).toNat))
  else acc
termination_by e - q

/-- The MAC loop in `Nat` arithmetic (`W2C.mulTop` on the 31-bit halves), for kernels `K ≥ 2^63` (never met by the
kernels of a run, see `macLoop`). -/
def macLoopN (lower : Bool) (rst rm : Array Nat) (k1 k0 off : Nat) (q e : Nat) (acc : Array Nat) : Array Nat :=
  if q < e then
    let v := rm[q]!
    let D := rst[q]! + off
    macLoopN lower rst rm k1 k0 off (q + 1) e (acc.set! D (acc[D]! + mulTop lower (v >>> 31) (v &&& m31) k1 k0))
  else acc
termination_by e - q

/-- Loop over the segments `[s, nseg)` of a row (previous cells `ca`); the triple entry of `(ca, cb, cc)` is at
`base + (ca / NT) * ND - ca % NT`, where `base = T3I` of `(ib, ic, dbc, ia = 0, dab = itb)`.  Kernels `K < 2^63` use the
`UInt64` loop `macLoop`, larger ones the `Nat` loop `macLoopN` (same values).  A segment whose end exceeds the row arrays
(never, for the rows built here) is skipped. -/
def segLoop (lower : Bool) (row : Row) (K3 : Array Nat) (base NT ND : Nat) (s nseg : Nat) (acc : Array Nat) :
    Array Nat :=
  if s < nseg then
    let ca := row.segCa[s]!
    let kk := K3[base + (ca / NT) * ND - ca % NT]!
    let k := kk >>> 1
    let q := row.segStart[s]!
    let e := row.segStart[s + 1]!
    let acc :=
      if h : e ≤ row.st.size ∧ e ≤ row.m.size then
        if k >>> 63 == 0 then
          macLoop lower row.st row.m (k >>> 31).toUInt64 (k &&& m31).toUInt64 (NS * (kk % 2)) e h.1 h.2 q acc
        else macLoopN lower row.st row.m (k >>> 31) (k &&& m31) (NS * (kk % 2)) q e acc
      else acc
    segLoop lower row K3 base NT ND (s + 1) nseg acc
  else acc
termination_by nseg - s

/-- The transitions, for the states `D ∈ [D, NS)` and both T classes, of the per-state sums `acc` (index `D + NS T`):
`g[δ(D; ns + T)] += acc[D + NS T]` for `δ` alive, and `g[NS] += close2(D; ns + T) · acc[D + NS T]`. -/
def transLoop (acc : Array Nat) (ns : Nat) (D : Nat) (g : Array Nat) : Array Nat :=
  if D < NS then
    let a0 := acc[D]!
    let a1 := acc[D + NS]!
    let i0 := D * 8 + ns
    let D0 := trs[i0]!
    let D1 := trs[i0 + 1]!
    let g := if D0 < NS then g.set! D0 (g[D0]! + a0) else g
    let g := if D1 < NS then g.set! D1 (g[D1]! + a1) else g
    transLoop acc ns (D + 1) (g.set! NS (g[NS]! + cls[i0]! * a0 + cls[i0 + 1]! * a1))
  else g
termination_by NS - D

/-- The accumulator `g` (size `NS + 1`) of the target `cc` from the row of `cb`: entry `D' < NS` collects the products
with `δ(D; N, S, T) = D'`, entry `NS` the products times `close2` (scale: entries of the row times `2^-76`). -/
def accOf (lower : Bool) (rd : RecData3) (rows : Array Row) (cc cb : Nat) : Array Nat :=
  let NT := rd.NT
  let ic := cc / NT
  let ib := cb / NT
  let itb := cb % NT
  let dbcN := cc % NT + (NT - 1) - itb
  let pbc := (ib * rd.NR + ic) * rd.ND + dbcN
  let base := (pbc * rd.NR) * rd.ND + itb + (NT - 1)
  let row := rows[cb]!
  let acc := segLoop lower row rd.K3 base NT rd.ND 0 row.segCa.size (Array.replicate (2 * NS) 0)
  transLoop acc (rd.nb[ic]! + rd.sb[pbc]!) 0 (Array.replicate (NS + 1) 0)

/-- The entries `(D', acc[D'] · wc)` with `acc[D'] ≠ 0`, `D' ∈ [D, NS)`, appended to `st`, `m`. -/
def emitLoop (acc : Array Nat) (wc : Nat) (D : Nat) (st m : Array Nat) : Array Nat × Array Nat :=
  if D < NS then
    let a := acc[D]!
    if a != 0 then emitLoop acc wc (D + 1) (st.push D) (m.push (a * wc)) else emitLoop acc wc (D + 1) st m
  else (st, m)
termination_by NS - D

/-- Append the segment of previous cell `cb` (the nonzero entries of `acc` times `wc`; none if all are `0`). -/
def pushSeg (r : Row) (cb wc : Nat) (acc : Array Nat) : Row :=
  let ⟨sca, sst, st, m⟩ := r
  let n0 := st.size
  let (st, m) := emitLoop acc wc 0 st m
  if st.size == n0 then ⟨sca, sst, st, m⟩ else ⟨sca.push cb, sst.push st.size, st, m⟩

/-- Loop over the source rows `cb ∈ [cb, NC)` of the target `cc`: the new row (not built if `last`) and the sum of the
closing entries. -/
def cbLoop (lower : Bool) (rd : RecData3) (rows : Array Row) (cc wc NC : Nat) (last : Bool) (cb : Nat) (r : Row)
    (cs : Nat) : Row × Nat :=
  if cb < NC then
    let acc := accOf lower rd rows cc cb
    let r := if last then r else pushSeg r cb wc acc
    cbLoop lower rd rows cc wc NC last (cb + 1) r (cs + acc[NS]!)
  else (r, cs)
termination_by NC - cb

/-- The new row of the target `cc` (entries at scale `2^-(E - 14 + PR)` for rows at scale `2^-E`) and its closing sum
(twice the closing value, same scale). -/
def targetRow (lower : Bool) (rd : RecData3) (rows : Array Row) (last : Bool) (cc : Nat) : Row × Nat :=
  let wc := rd.w[cc / rd.NT]!
  let (r, cs) := cbLoop lower rd rows cc wc (rd.NR * rd.NT) last 0 Row.empty 0
  (r, cs * wc)

/-- the target of the half index `h < NR * (NT/2)`: ring `h / (NT/2)`, slot `NT/2 + h % (NT/2)` -/
@[inline] def halfCell (NT h : Nat) : Nat := (h / (NT / 2)) * NT + NT / 2 + h % (NT / 2)

/-- mirror image of a cell: slot `it ↦ NT - 1 - it` -/
@[inline] def mirC (NT c : Nat) : Nat := (c / NT) * NT + (NT - 1 - c % NT)

/-- The rows of all cells from the rows of the half: the row of a cell `c` with slot `< NT/2` is the row of `R c`
with every previous cell `ca` replaced by `R ca`. -/
def fullRows (NR NT : Nat) (half : Array Row) : Array Row :=
  (Array.range (NR * NT)).map fun c =>
    let it := c % NT
    let H := NT / 2
    if H ≤ it then half[(c / NT) * H + (it - H)]!
    else
      let r := half[(c / NT) * H + (NT - 1 - it - H)]!
      { r with segCa := r.segCa.map (mirC NT) }

/-- Global normalisation to mantissas `< 2^62`: the rows and the shift `sh` (the scale exponent drops by `sh`). -/
def normRows (lower : Bool) (rows : Array Row) : Array Row × Nat :=
  let mx := rows.foldl (fun acc r => r.m.foldl Max.max acc) 0
  let sh := if nbits mx > 62 then nbits mx - 62 else 0
  if sh == 0 then (rows, 0)
  else (rows.map fun r => { r with m := r.m.map fun v => rnd lower v sh }, sh)

/-- Levels `i → i + 1` with fuel `n` (`last` at fuel `1`); `rows` = level `i` for all cells, at scale `2^-E`.  Appends
`(value, scale)` with `value · 2^-scale` a bound of `Φ_{i+2}`: the sum over the computed half of the closing sums. -/
def recIter3 (lower : Bool) (rd : RecData3) (par : Bool) : Nat → Array Row → Int → List (Nat × Int) →
    List (Nat × Int)
  | 0, _, _, out => out
  | n + 1, rows, E, out =>
    let res := pgen par (rd.NR * (rd.NT / 2)) (rd.NR * (rd.NT / 2)) fun h =>
      targetRow lower rd rows (n == 0) (halfCell rd.NT h)
    let phi := res.foldl (fun acc rc => acc + rc.2) 0
    let out' := out ++ [(phi, E - 14 + (PR : Int))]
    let (half, sh) := normRows lower (res.map (·.1))
    recIter3 lower rd par n (fullRows rd.NR rd.NT half) (E - 14 + (PR : Int) - (sh : Int)) out'

/-- Level 2 for the target `c2`, loop over `c1 ∈ [c1, NC)`: entries `(c1, D', w(c2) · ⌊w(c1) f1(c1) k2(c1, c2) / 2^62⌋)`
(scale `2^-(2 PR + 62)`) and the sum of `close2 · ⌊w(c1) f1(c1) k2(c1, c2) / 2^62⌋` (scale `2^-(PR + 62)`). -/
def c1Loop (lower : Bool) (rd : RecData3) (f1 k2 : Array Nat) (ir2 it2 n2 w2 NC : Nat) (c1 : Nat) (r : Row) (cs : Nat) :
    Row × Nat :=
  if c1 < NC then
    let ir1 := c1 / rd.NT
    let D := trs[rd.nb[ir1]!]!
    if D < NS then
      let pi := (ir1 * rd.NR + ir2) * rd.ND + (it2 + (rd.NT - 1) - c1 % rd.NT)
      let v := mul62 lower (rd.w[ir1]! * f1[ir1]!) k2[pi]!
      let idx := D * 8 + n2 + rd.sb[pi]!
      let D2 := trs[idx]!
      let r := if D2 < NS && v != 0 then
          let ⟨sca, sst, st, m⟩ := r
          ⟨sca.push c1, sst.push (st.size + 1), st.push D2, m.push (v * w2)⟩
        else r
      c1Loop lower rd f1 k2 ir2 it2 n2 w2 NC (c1 + 1) r (cs + cls[idx]! * v)
    else c1Loop lower rd f1 k2 ir2 it2 n2 w2 NC (c1 + 1) r cs
  else (r, cs)
termination_by NC - c1

/-- Level 2 (all cells `c2`, rows at scale `2^-(2 PR + 62)`) and `Φ_3`: half the sum of the closing sums times `w(c2)`
(the value is the sum, at scale `2^-(2 PR + 62 + 1)`). -/
def level2 (lower : Bool) (rd : RecData3) (f1 k2 : Array Nat) (par : Bool) : Array Row × Nat :=
  let NC := rd.NR * rd.NT
  let res := pgen par 256 NC fun c2 =>
    let ir2 := c2 / rd.NT
    let w2 := rd.w[ir2]!
    let (r, cs) := c1Loop lower rd f1 k2 ir2 (c2 % rd.NT) rd.nb[ir2]! w2 NC 0 Row.empty 0
    (r, cs * w2)
  (res.map (·.1), res.foldl (fun acc rc => acc + rc.2) 0)

/-- The triple kernels for `t_j` and the direction: `2 · K + T`, `K = e1^j` (directed). -/
def mkK3 (r : Run3) (lower : Bool) (j : Nat) (par : Bool) : Array Nat :=
  pgen par 256 r.e1lo.size fun i =>
    let v := r.e1lo[i]!
    2 * powK lower (if lower then v / 2 else r.e1hi[i]!) j + v % 2

/-- The recursion for `t = j 2^-dtl` and one direction: `(value, scale)` for `k = 3, ..., kmax`, `value · 2^-scale` a
lower (`lower`) or upper bound of `Φ_k(t)` for the stored tables. -/
def runT3 (r : Run3) (lower : Bool) (j dtl kmax : Nat) (par : Bool) : List (Nat × Int) :=
  let g := r.g
  let rd : RecData3 := ⟨g.NR, g.NT, g.ND, r.rings.map (·.areaLo.toNat),
    r.rings.map (fun R => if R.nflag then 4 else 0), r.pairs.map (fun p => if p.scls then 2 else 0),
    mkK3 r lower j par⟩
  let f1 : Array Nat := r.rings.map fun R => kern lower j dtl (upq R.euHi dtl)
  let k2 : Array Nat := pgen par 64 r.ab2.size fun i => kern lower j dtl r.ab2[i]!
  let (rows, phi3) := level2 lower rd f1 k2 par
  let (rowsN, sh) := normRows lower rows
  recIter3 lower rd par (kmax - 3) rowsN ((2 * PR + 62 : Nat) - (sh : Int)) [(phi3, ((2 * PR + 62 + 1 : Nat) : Int))]

/-! ## Checks -/

/-- A shard: the run data, then for each claim both directed recursions, and the check of the claims (`W2C.TClaim`:
`(j, [(k, loM, loE, hiM, hiE)])` for `loM 2^-loE ≤ Φ_k(t_j) ≤ hiM 2^-hiE`). -/
def shard3OK (g : Grid) (dtl kmax : Nat) (par : Bool) (cs : List TClaim) : Bool :=
  let r := mkRun3 g dtl par
  cs.all fun c => checkClaims kmax (runT3 r true c.1 dtl kmax par).toArray (runT3 r false c.1 dtl kmax par).toArray c

/-- Claims from outputs, rounded outward to `bits` significant bits. -/
def claimOf (j bits : Nat) (lo hi : List (Nat × Int)) : TClaim :=
  (j, (List.range lo.length).map fun k0 =>
    let (lm, le) := lo.getD k0 (0, 0)
    let (hm, he) := hi.getD k0 (0, 0)
    let sl := nbits lm - Min.min (nbits lm) bits
    let sh := nbits hm - Min.min (nbits hm) bits
    (k0 + 3, lm >>> sl, le - sl, (hm + 2 ^ sh - 1) >>> sh, he - sh))

end W3C
