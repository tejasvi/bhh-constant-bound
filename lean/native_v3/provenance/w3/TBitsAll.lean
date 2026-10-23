import W3Cert.Rec3
open W3C W2C BHH.Cert

/-- T bits of all triple entries in the order (ia, ib, ic, dab, dbc) (dab, dbc from -(NT-1)), as mkTri stores them
(Lean's computed half dbc > 0 ∨ (dbc = 0 ∧ dab ≥ 0), the other half copied from the mirror), one byte each. -/
def main (args : List String) : IO Unit := do
  let n1 := (args.getD 0 "20").toNat!
  let n2 := (args.getD 1 "10").toNat!
  let nt := (args.getD 2 "48").toNat!
  let out := args.getD 3 "tbits_lean.bin"
  let g : Grid := ⟨n1, n2, nt, 64, false⟩
  let td := mkTabData g
  let NR := g.NR
  let NT := g.NT
  let ND := g.ND
  let tbit (ia ib ic : Nat) (dabN dbcN : Nat) : UInt8 :=
    let (dabN, dbcN) := if canon3 NT dbcN dabN then (dabN, dbcN) else (ND - 1 - dabN, ND - 1 - dbcN)
    let dab : Int := Int.ofNat dabN - Int.ofNat (NT - 1)
    let dbc : Int := Int.ofNat dbcN - Int.ofNat (NT - 1)
    let (_, mx) := triRange28 (geoAt g td.geo ia 0).pv (geoAt g td.geo ib dab).pv (geoAt g td.geo ic (dab + dbc)).pv
    if mx ≤ ONE then 1 else 0
  let blocks := (List.range (NR * NR * NR)).map fun pr => Task.spawn fun _ =>
    let ia := pr / (NR * NR)
    let ib := (pr / NR) % NR
    let ic := pr % NR
    ByteArray.mk ((Array.range (ND * ND)).map fun q => tbit ia ib ic (q / ND) (q % ND))
  let h ← IO.FS.Handle.mk out IO.FS.Mode.write
  for t in blocks do
    h.write t.get
  h.flush
  IO.println s!"wrote {NR * NR * NR * ND * ND} bytes"
