# Regenerating `W3Prod20/Claims.lean`

From the root of the release tree, one command:

    bash provenance/w3/regen_claims.sh

Prerequisites: the Lean toolchain named in `lean-toolchain` (through elan), gcc with OpenMP, FLINT 3 with MPFR and GMP, and
python3. The script writes only into its work directory: `_w3regen` in the current directory (the release tree) by default,
or `$W3_REGEN_DIR` if that is set; there it removes and recreates the subdirectories `tools` and `out`. It changes no other
file. For a read-only copy of the tree, set `W3_REGEN_DIR` to a writable directory outside it. The script stops at the
first failing step and ends with `REGENERATED W3Prod20/Claims.lean: all checks passed` when every sha256 below matches.
On a 128-vCPU machine the full run took about 20 minutes (T classes 5 min, evaluator 11.5 min, the rest a few minutes);
it needs a few GB of memory.

## What it does
1. Builds two small Lean programs, `TBitsAll.lean` and `TintCalc.lean`, in a separate Lake project from the release tree's
   `BHHCert/`, `W2Cert/` and `W3Cert/` (core Lean only, no Mathlib).
2. `tbitsall 20 10 48`: the T class of every triple entry, computed by the Lean code of `W3Cert` (one byte per entry).
3. Compiles the window-3 C evaluator (`w3_arb_dump.c` with `w3conn_auto.h`) and runs it on the grid (20,10,48), with the
   T classes of step 2 loaded through its `W3TLOAD` option (24 threads by default; `W3_NTH` changes this).
4. `phi_to_claims.py`: the claims, the evaluator's values widened by the relative margins 1e-7 (lower) and 1e-5 (upper)
   into 64-bit-mantissa enclosures; `tintcalc`: the t-integral target num/den, appended to the claims file as its
   `NUMDEN` line.
5. `gen_prod.py`: writes the modules, then compares `Claims.lean`, `Grid.lean`, `TInt.lean` and `Nondeg.lean` with the
   expected sha256 below and with the copies in the release tree. `S00.lean` and `Final.lean` are not compared: the
   release's `S00.lean` was written by an earlier version of the generator (with the filter `0 < c.1`, which keeps every
   claim since all claims have `j ≥ 1`), and `Final.lean` was edited afterwards.

## Expected sha256, grid (20,10,48)
| file | sha256 |
|---|---|
| `tbits.bin` (243,675,000 bytes) | `f11e6ed9f2491efb3177c4ea23cb4c500fbc9206d4c2a4a03dd248fb12423fac` |
| `phi_values.txt` (the 960 `PHI` lines of the evaluator output) | `bf8db7bebac5fd2197d39963cb5d5443547898d82746ec8c46aa7b96666bce75` |
| `claims.txt` (claims plus the `NUMDEN` line) | `d0dff06b0f72941cd1a0a17def6aabc01eee6515adb674f0feff31129ca8fb38` |
| `tint.txt` | `cb5f3b7341016661e49cfd1a689a208ee37baa88a5bb53f102f286e18eff2dc2` |
| `W3Prod20/Claims.lean` | `e7156d0609bc98dee12458e9c01730c12c8109dca8d09864dfcbf234edd6d171` |
| `W3Prod20/Grid.lean` | `56f451341fa595de09c45353ded79a3be213b5d44539c5041dd51620c713befc` |
| `W3Prod20/TInt.lean` | `0a0ae6db1158e3885463d71563ef0948a7ecf39b56fe9243499258b8f5e5e142` |
| `W3Prod20/Nondeg.lean` | `e3efd887fb314e5fbd6bb5fd2667a365660f95c9d25879514055e1470b393d3d` |

The evaluator's last output line reports its run time, so the whole output file differs from run to run; its `PHI` values
do not. On the test grids (6,3,12) and (10,5,24) they were identical across 1 and 8 threads and across repeated runs.

`bash provenance/w3/regen_claims.sh 6 3 12` runs the same steps on a small grid in a few minutes and prints the sha256s
instead of checking them.

## Role of the claims
The claims are untrusted input. The shard `W3Prod20.S00` recomputes the tables and both directed recursions in Lean and
checks every claim, so a wrong claim makes the shard fail and cannot make the theorem false. This recipe documents where
the claims came from; checking the proof does not need it.

## Files
- `regen_claims.sh`: the recipe.
- `w3_arb_dump.c`, `w3conn_auto.h`: the C evaluator of the window-3 certificate with its optional environment hooks:
  `W3TLOAD` (load the T classes from a file; used here); `W3DUMP`, `W3DUMPT`, `W3DUMP3` (dump tables); `W3SLICE`,
  `W3SAVE` (distributed table builds); `W3FLOAT`, `W3CTRL` (validation and negative controls). The last three groups are
  unused here.
- `TBitsAll.lean`: the T classes from the Lean code. `TintCalc.lean`: the t-integral of a claims file, by the Lean code of
  `TInt.lean`'s check.
- `phi_to_claims.py`: evaluator output to claims. `gen_prod.py`: claims to the modules of `W3Prod20/`.
