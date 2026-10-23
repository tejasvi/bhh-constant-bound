# Native proof of beta >= 0.6496497227: final assembly

`BHH/BetaN3W20.lean`:

    theorem BHH.betaBoundV3At_N_w20 : BetaBoundV3At (6496497227 / 10 ^ 10) :=
      W3Prod20.beta_bound mainBoundsV3_N
    theorem BHH.bhhBetaBoundV3At_N_w20 : BHHBetaBoundV3At (6496497227 / 10 ^ 10) :=
      W3Prod20.bhh_beta_bound mainBoundsV3_N

`BHH.mainBoundsV3_N : MainBoundsV3` (`BHH/MainN3.lean`, the C_k part below): `C_3 ≥ 0.0117130195`, `C_4 ≥ 0.0063707166`,
`C_5 ≥ 0.0035280362`. `W3Prod20.w3_bound_lit : W3BoundAt (30379504113 / 10000000000000)` (`W3Prod20/Final.lean`, the
window-3 part below): `Σ_{k=6}^{22} C_k ≥ 0.0030379504113`. `W3Prod20.beta_bound` combines them with
`BHH.W3.betaBoundV3At_of` (`W3/Assembly.lean`): `β ≥ 5/8 + C_3 + C_4 + C_5 + 0.0030379504113 ≥ 0.6496497227`. All statements
are in `BHH/StatementW3.lean`, under `GreenFormula` and `VertexLemmaSeg` (and `DongCaoK30` in the β bounds).
`BHH/BetaN3.lean` also gives `betaBoundV3At_N_of : 0 ≤ w → b ≤ 5/8 + C₃ + C₄ + C₅ + w → W3BoundAt w → BetaBoundV3At b`
(constants as certified), its `BHHBetaBoundV3At` form, and the paper-constant forms `betaBoundV3_N_of : W3Bound →
BetaBoundV3`, `bhhBetaBoundV3_N_of : W3Bound → BHHBetaBoundV3`; `W3Bound` (the constant of the grid (60,30,144)) stays a
hypothesis there and is not proved in this tree.

## Axioms

`axioms_N3W20.txt` is the output of `lean BHH/AxN3W20.lean`. The two theorems depend on `propext`, `Classical.choice`,
`Quot.sound` and `native_decide` auxiliary axioms only: 5,671 in all. 5,667 are those of the C_k part: `BHH.Shards.k3_s*`
(62), `k4_s*` (1,142) and `k5r2_s*` (4,457), one per shard, and the g-table checks `BHH.gtN_nonneg_D3/D4/D5`,
`BHH.E.gtN_check_three/four/five`. 4 are those of the window-3 part: `W3Prod20.shard00`, `tint`, `nondeg`, `chpos`.
`axioms_N3.txt` (`lean BHH/AxN3.lean`) lists the C_k part alone.

## Files

`SHA256SUMS` lists every file except itself and `README.md`. The `.lean` files are the import closure of `BHH/AxN3W20.lean`,
`BHH/AxN3.lean` and `W3Prod20/AxFinal.lean`, plus the roots `BHHCert.lean`, `W2Cert.lean` and `W3Cert.lean` of the
precompiled libraries and the module `BHHCert/CandK.lean` that the root `BHHCert.lean` adds: 6,200 files (BHH 76, BHHCert 12
+ the root, BHHShard 5,997: K3 64, K4 1,155, K5R2 4,778; W2 57; W2Cert 6 + the root; W3 39; W3Cert 3 + the root; W3Prod20 7).
The only external import is `Mathlib`. `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: Lean v4.35.0-rc3, Mathlib
c55e6e786f49. `tools/`: the closure check, the kernel replay tool and the C checker used for the claims of the C_k part.
`provenance/w3/`: the pipeline that produced the claims of the window-3 part (8 files; its two Lean files are stand-alone
tools, not part of the proof). The
scripts that planned the shards and checked the per-range sums are not included: the claims are untrusted lower bounds,
every shard file is included, and the chain types force the ranges to be contiguous. The comments and docstrings of some
files were edited after the build (internal labels removed); compiling those modules again gives the same declarations
(in `W3Cert/Rec3.lean` the equation lemmas of the recursive functions record the source positions of their recursive calls
as metadata, which moved with the edit; without the metadata the declarations are the same).

## The C_k part

* `C_3`, `C_4`: the shards `BHHShard/K3`, `BHHShard/K4` and their chains are those of the native proof of version 2 of the paper (`lean/native`).
* `C_5`: the decisions of the refined C5 run (`k = 5`, `W0 0.6`, `WF 0.00025`, `EPS 1e-13`, `ninit 4194304`) are the context
  `ctx5r2` of `BHHCert/ShardR2.lean`, with `shardN5r2 a b = shardSum 5 (floatDec ctx5r2) (Lk 5) (RN 5) a b`. Every range
  `[16384 s, 16384 (s+1))` of the checker run was cut into Lean shards `BHHShard/K5R2/S*.lean`,
  `theorem k5r2_s… : (v : Int) ≤ BHH.Cert.shardN5r2Par pd a b := by native_decide` (`pd = 8`, or `12` for single heavy
  boxes), no shard crossing a range. The claims are floor(Σ main × (1 − 10⁻⁹)) − 1 per shard (units 2⁻²⁵⁶) from a first
  pass of the C checker (`tools/chk_box.c`, per-box sums); per range, the per-box sums equal the checker run's
  `main_floor1e30` to 1.3 × 10⁻¹⁷ relative. The shards were compiled with `lean -o`, with the native libraries of `BHHCert`
  (and modules `TreePar`, `ShardR2`) loaded, on up to about 100 machines with 32 to 96 threads each (4,457 shards; the C first
  pass and the Lean shards took about 5 h in all).
* Chains (`BHH/ShardChainR2.lean`: consecutive ranges add up): `BHHShard/K5R2/L{sss}.lean` gives
  `k5r2_l{sss} : (V_s : Int) ≤ shardN5r2 (16384 s) (16384 (s+1))` for each range `s` (through parts `G{sss}_{pp}`
  for the 20 ranges with more than 100 items), `Q0`-`Q3` chain 64 ranges each and `All.lean` gives
  `k5r2_all : (S : Int) ≤ shardN5r2 0 (2 ^ RN 5)` (4,457 shards and 1,613 ranges of boxes with no claim, by
  `shardN5r2_nonneg`); `C5_ge_of_shardN5r2` turns it into `C_5 ≥ 0.0035280362` (relative headroom 2.5 × 10⁻⁸).

## The window-3 part

* `W3Prod20/Final.lean`: `w3_bound : W3BoundAt (num / den)` by `BHH.W3.w3BoundAt_of_checks` (`W3/Final3Of.lean`) from the
  theorems of the proof modules in `W3/` (the pass, the Laplace transform and area bound, the discretisation bound, the
  triple-entry primitives and entries, the table soundness and the recursion soundness; their interfaces are the `Prop`s of
  `W3/Interfaces.lean`), the window-2 modules in `W2/`, and four native checks:
  * `shard00` (`W3Prod20/S00.lean`): `W3C.shard3OK grid dtl kmax true (claims.filter (fun c => decide (0 < c.1))) = true`.
    It recomputes the tables (pair entries, symmetrised; triple entries by exact fixed-point interval arithmetic, the
    computed half and the mirrored half) and both directed recursions at every claimed point `t_j`, and checks the claimed
    enclosures of `Φ^d_k(t_j)`, `3 ≤ k ≤ 22`;
  * `tint` (`W3Prod20/TInt.lean`): the t-integral of the claims, `Σ_{k=6}^{22} C_k ≥ num/den`;
  * `nondeg`, `chpos` (`W3Prod20/Nondeg.lean`): the nondegeneracy check of the grid (rings and the vertex paths of the pair
    entries) and `0 < (mkAData grid).ch.lo`.
* The grid `(20,10,48)` is `W3Prod20/Grid.lean`. The claims (`W3Prod20/Claims.lean`) are enclosures
  `loM 2^-loE ≤ Φ^d_k(t_j) ≤ hiM 2^-hiE` for `3 ≤ k ≤ 22`, `t_j = j/8`, `1 ≤ j ≤ 48`: untrusted values from the C evaluator of
  the window-3 certificate, run with the triple-entry classes of this Lean code; `shard00` checks every one of them.
  `bash provenance/w3/regen_claims.sh` (`provenance/w3/RECIPE.md`) regenerates `Claims.lean`, `Grid.lean`, `TInt.lean` and
  `Nondeg.lean` byte for byte in a work directory (`./_w3regen`, or `$W3_REGEN_DIR`): the Lean T classes (`TBitsAll.lean`),
  the C evaluator (`w3_arb_dump.c`, `w3conn_auto.h`; FLINT 3), `phi_to_claims.py`, the t-integral target (`TintCalc.lean`)
  and the generator `gen_prod.py` (about 20 min on 128 threads).
* `W3Cert/` is the computational code of these checks (core Lean, compiled to native code). `W2/`, `W2Cert/` and
  `BHH/TwoDisk.lean` are the window-2 modules that the window-3 proof uses, the same files as in the native proof of
  version 2 of the paper (`lean/native`).
* `shard00` took 12,702 s on a 96-thread machine; `tint`, `nondeg` and `chpos` take about 20 s each.

## Build route

`lakefile.toml` defines the libraries `BHH`, `BHHCert`, `W2`, `W2Cert`, `W3`, `W3Cert` and `W3Prod20`. `lake build` covers
all their modules except `BHH/MainN3.lean`, `BHH/BetaN3.lean`, `BHH/AxN3.lean`, `BHH/BetaN3W20.lean` and
`BHH/AxN3W20.lean`, which import shard modules; it evaluates the `native_decide` checks of `W3Prod20/S00.lean`, `TInt.lean`
and `Nondeg.lean` with the native libraries of `W3Cert`, `W2Cert` and `BHHCert`. The other modules are compiled with plain
`lean -o` (`-R .`, the options of `lakefile.toml` as `-D` flags, `LEAN_PATH` from `lake env printenv LEAN_PATH`), in this
order:
1. the shards `BHHShard/K3/S*`, `BHHShard/K4/S*` and `BHHShard/K5R2/S*`, each with `--load-dynlib` of the native
   libraries that its `native_decide` evaluates (`libBHH_BHHCert.so`, and for the `shardNPar`/`shardN5r2Par` shards also
   the module libraries `BHH_BHHCert_TreePar.so` and, for K5R2, `BHH_BHHCert_ShardR2.so`, all built by `lake build`);
2. the chains: `BHHShard/K3/G*` then `BHHShard/K3/All`; `BHHShard/K4/G*` then `BHHShard/K4/All`; `BHHShard/K5R2/G*`,
   then `L*`, then `Q*`, then `BHHShard/K5R2/All`;
3. `BHH/MainN3.lean`, `BHH/BetaN3.lean`, `BHH/AxN3.lean` (which prints `axioms_N3.txt`), `BHH/BetaN3W20.lean` and
   `BHH/AxN3W20.lean` (which prints `axioms_N3W20.txt`).

## Kernel replay

`tools/ReplayMods.lean` (`Lean.Kernel.Environment.replay`, as in lean4checker) imports `Mathlib` and sends every constant
of the 6,197 modules that have an `.olean` (the closure without the axiom printers `BHH/AxN3.lean`, `BHH/AxN3W20.lean` and
`W3Prod20/AxFinal.lean`, plus the three library roots and `BHHCert/CandK.lean`) to the kernel again: 18,802 constants were
checked and none was rejected or missing. Skipped by `replay` (unsafe compiler auxiliaries and partial definitions): 36
constants.
