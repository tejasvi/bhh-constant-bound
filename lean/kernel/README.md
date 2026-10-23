# Lean 4 proof of beta >= 0.6440396 (kernel only, standard axioms)

Theorems (`BHH/MainK3.lean`):

    theorem BHH.mainBoundsK3   : MainBoundsK3    -- C_3 >= 0.0117130195, C_4 >= 0.0059365909, C_5 >= 0.00139
    theorem BHH.betaBoundK3    : BetaBoundK3     -- beta >= 0.6440396 for every beta with DongCaoK30 beta
    theorem BHH.bhhBetaBoundK3 : BHHBetaBoundK3  -- the same for the BHH constant

The label K3 in the names (`MainK3`, `MainBoundsK3`, `AXIOMS_K3.txt`, `AxK3.lean`, ...) marks this kernel-only proof;
it reuses the trees of C_3 and C_4 of the kernel-only proof K2 (`BHH/KSub2`, names with K2) and adds a coarse tree of
C_5 (`BHH/KSub3`). The statements are in `BHH/StatementK3.lean`. They use the objects and the three named hypotheses of
the native proof: `GreenFormula` (`BHH/Defs.lean`), `VertexLemmaSeg` and `DongCaoK30` (`BHH/DefsV2.lean`).
`DongCaoK30 beta` says beta >= 5/8 + sum_{k=3}^{30} C_k (Theorem 3 of Dong and Cao with K = 30). The theorem for the BHH
constant assumes `DongCaoK30 beta` for every beta with `IsBHHConstant beta`.

The tree of C_3 is the subdivision of the paper's run for k = 3 (W0 0.1, Wf 0.0002, tol 1e-12, 4,096 initial boxes),
so `mainBoundsK3` proves the paper's bound for C_3 by kernel evaluation. C_4 uses a coarser tree (W0 0.4, Wf 0.002,
tol 3e-10, 512 initial boxes) and C_5 a coarse tree (W0 0.6, Wf 0.0005, tol 3e-10, 4,194,304 initial boxes). The table
of g for k = 5 is checked by the kernel as well (`gtK_sound_five`, `BHH/GraphK5.lean`).

Axioms (`AXIOMS_K3.txt`, printed by `lake env lean AxK3.lean`): `propext`, `Classical.choice`, `Quot.sound` only.
Every leaf value is computed by the Lean kernel (`decide +kernel`). Some imported modules that the native proof also
uses contain `native_decide` lemmas; the theorems above do not use them, as the axiom list shows.

Files:
- the import closure of `BHH/MainK3.lean` without the generated modules `BHH/KSub2/**` (51,282 files) and `BHH/KSub3/**`
  (53,973 files), which are not shipped, and the library root `BHHCert.lean`;
- `AxK3.lean`, which prints the axioms and the statements (its output is `AXIOMS_K3.txt`);
- the untrusted cut generators `BHHCert/KCutGen2.lean` (C_3, C_4) and `BHHCert/KCutGen3t.lean` (C_5) and the module both
  import for the tree codes, `BHHCert/TreeKGen.lean` (no proof module imports them); `lakefile_kcut2_snippet.toml` and
  `lakefile_kcut3t_snippet.toml` declare their executables `kcut2` and `kcut3t`;
- the untrusted module writers `tools/gen_kcut.py` (C_3, C_4) and `tools/gen_kcut5.py` (C_5), and `tools/canon_kc5.py`,
  which merges the C_5 generator outputs; their parameters and commands are in `GEN_PARAMS.txt`;
- `KSub2_SHA256SUMS` and `KSub3_SHA256SUMS` (sha256 of the generated files), and `kc2/RECORDS_SHA256`,
  `kc2/UNCOMPRESSED_SHA256`, `kc5/RECORDS_SHA256`, `kc5/UNCOMPRESSED_SHA256` (sha256 of the cut data, compressed and
  uncompressed);
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, and `SHA256SUMS` (sha256 of every file except itself and
  this README).

`lakefile.toml` also declares development executables (`bnbfloat`, `exacttest`, `uniontest`, `benchtest`,
`bnbdriver`, `treedriver`, `leafdump`, `profile`) whose sources are not included; neither the proof nor the generators
use them.

Cut data: k3_all.txt, k4_all.txt (C_3, C_4) and c5_all.txt (C_5) are published with the paper's data, compressed, as
`k3_all.txt.xz`, `k4_all.txt.xz` and `c5_all.txt.xz` (sha256 of the .xz files in `kc2/RECORDS_SHA256` and
`kc5/RECORDS_SHA256`, of the uncompressed files in `kc2/UNCOMPRESSED_SHA256` and `kc5/UNCOMPRESSED_SHA256`). To regenerate
the modules, put the first two .xz files into `kc2/` and the third into `kc5/`; then, from this directory, run
`(cd kc2 && sha256sum -c RECORDS_SHA256 && xz -dk k3_all.txt.xz k4_all.txt.xz && sha256sum -c UNCOMPRESSED_SHA256)` and
`(cd kc5 && sha256sum -c RECORDS_SHA256 && xz -dk c5_all.txt.xz && sha256sum -c UNCOMPRESSED_SHA256)`, the commands in
`GEN_PARAMS.txt`, and `sha256sum -c KSub2_SHA256SUMS KSub3_SHA256SUMS`. The generated modules hold 3,033,594 chunk
theorems `subOK k L chunk = true`, each proved by `decide +kernel`: 645,003 for C_3 and 334,439 for C_4 (at most 25 leaves
each) and 2,054,152 for C_5 (at most 12 leaves each), with 35,337,851 leaves in all (11,563,336, 5,970,794 and
17,803,721). One more theorem `top : cutOK ...` per initial box with leaves (2,592 for C_3 and C_4, 19,287 for C_5), also
proved by `decide +kernel`, checks the top part of its cut tree against the claims of its pieces. To rerun the generators
themselves, append the two snippet files to `lakefile.toml` and follow step 1 of each part of `GEN_PARAMS.txt`.

Build: Lean v4.35.0-rc3 and Mathlib c55e6e786f49 (`lean-toolchain`, `lake-manifest.json`). After regenerating the
modules, run `lake build BHH.MainK3`, then `lake env lean AxK3.lean`. The chunk modules do not depend on each other and
can be built in parallel.
