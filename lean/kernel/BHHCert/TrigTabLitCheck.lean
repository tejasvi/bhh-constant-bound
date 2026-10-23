/-
The literal cos/sin table (BHHCert/TrigTabLit.lean) is `cosSin` at every grid point: one kernel check per table row
(64 evaluations of `cosSin` each; a single declaration for all 1,793 points makes the kernel's caches grow superlinearly).
-/
import BHHCert.TrigTabLit

namespace BHH.Cert

set_option maxRecDepth 100000 in
theorem csLit_row0 : (List.range' 0 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row1 : (List.range' 64 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row2 : (List.range' 128 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row3 : (List.range' 192 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row4 : (List.range' 256 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row5 : (List.range' 320 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row6 : (List.range' 384 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row7 : (List.range' 448 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row8 : (List.range' 512 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row9 : (List.range' 576 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row10 : (List.range' 640 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row11 : (List.range' 704 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row12 : (List.range' 768 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row13 : (List.range' 832 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row14 : (List.range' 896 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row15 : (List.range' 960 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row16 : (List.range' 1024 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row17 : (List.range' 1088 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row18 : (List.range' 1152 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row19 : (List.range' 1216 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row20 : (List.range' 1280 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row21 : (List.range' 1344 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row22 : (List.range' 1408 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row23 : (List.range' 1472 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row24 : (List.range' 1536 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row25 : (List.range' 1600 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row26 : (List.range' 1664 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row27 : (List.range' 1728 64).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem csLit_row28 : (List.range' 1792 1).all (fun j => ivPairEqB (csLit j) (cosSin ((j : Int) * 2 ^ (PR - TB)))) = true := by
  decide +kernel

end BHH.Cert
