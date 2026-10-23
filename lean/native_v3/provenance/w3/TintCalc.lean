import W2Cert.Shard
open W2C BHH.Cert

/-- The t-integral (`tintOK`'s total) of a claims file (`C j k loM loE hiM hiE` lines): prints `NUMDEN num den`. -/
def main (args : List String) : IO Unit := do
  let fn := args.getD 0 "claims.txt"
  let dtl := 3
  let T := 6
  let kmax := 22
  let lsub := 8
  let txt ← IO.FS.readFile fn
  let ntv0 := T * 2 ^ dtl
  let mut m : Array (Array (Nat × Nat × Int × Nat × Int)) := Array.replicate (ntv0 + 1) #[]
  for line in txt.splitOn "\n" do
    let p := (line.splitOn " ").filter (· ≠ "")
    if p.length == 7 && p[0]! == "C" then
      let j := p[1]!.toNat!
      let e : Nat × Nat × Int × Nat × Int := (p[2]!.toNat!, p[3]!.toNat!, p[4]!.toInt!, p[5]!.toNat!, p[6]!.toInt!)
      if j ≤ ntv0 then m := m.set! j (m[j]!.push e)
  let ntv := T * 2 ^ dtl
  let cs : List TClaim := (List.range ntv).map fun j0 => (j0 + 1, m[j0 + 1]!.toList)
  match claimLogs ntv kmax cs with
  | none => IO.println "claimLogs failed"
  | some (L, H) =>
    let logs := logTable (ntv * 2 ^ lsub) (dtl + lsub)
    let mut tot : Int := 0
    for k in [6:kmax + 1] do
      let c := ckLo k dtl ntv lsub L[k]! H[k]! logs
      tot := tot + c
      IO.println s!"K {k} {(c * 10 ^ 15) / ONE}e-15"
    let num := (tot * 10 ^ 13) / ONE
    IO.println s!"TOTAL sum_6..22 >= {(tot * 10 ^ 15) / ONE}e-15"
    IO.println s!"NUMDEN {num} 10000000000000 tintOK {tintOK dtl T kmax lsub cs num.toNat (10 ^ 13)}"
